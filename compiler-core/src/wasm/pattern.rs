use std::sync::Arc;

use ecow::EcoString;
use wasm_encoder::Instruction;

use crate::{
    analyse::Inferred,
    ast::{Pattern, TypedPattern},
    type_::{FieldMap, PatternConstructor},
};

use super::{
    encoder::WasmTypeImpl,
    environment::{Binding, Environment},
    integer, parse_float,
    string::unescape,
    table::{Local, LocalId, LocalStore, Strings, SumId, SymbolTable, TypeId},
};

#[derive(Debug, Clone)]
pub struct CompiledPattern {
    pub checks: Vec<Check>,
    pub assignments: Vec<Assignment>,
    pub nested: Vec<CompiledPattern>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Check {
    IntegerEquality {
        local: LocalId,
        value: i32,
    },
    FloatEquality {
        local: LocalId,
        value: f64,
    },
    ProductEquality {
        subject: LocalId,
        test_sum: SumId,
        discriminant: u32,
    },
    BooleanEquality {
        local: LocalId,
        value: bool,
    },
    StringEquality {
        local: LocalId,
        string: EcoString,
    },
    PrefixEquality {
        local: LocalId,
        prefix: EcoString,
    },
}

#[derive(Debug, Clone)]
pub enum Assignment {
    // Reassigns `subject_local` to `target_local` and creates a named binding `name`
    Named {
        name: EcoString,
        subject_local: LocalId,
        target_local: LocalId,
    },

    Cast {
        subject_local: LocalId,
        target_local: LocalId,
        target_type: TypeId,
    },

    /// Assigns a field of a struct to a local variable
    StructField {
        subject_local: LocalId,
        target_local: LocalId,
        field_index: u32,
        struct_type: TypeId,
    },

    /// Assigns a suffix of a string to a local variable
    StringSuffix {
        subject_local: LocalId,
        target_local: LocalId,
        name: EcoString,
        from: u32,
    },

    /// Assigns a string constant to a local variable
    StringConstant {
        constant: EcoString,
        target_local: LocalId,
        name: EcoString,
    },
}

pub fn compile_pattern(
    subject: LocalId,
    pat: &TypedPattern,
    table: &SymbolTable,
    env: &Environment<'_>,
    strings: &mut Strings,
    locals: &mut LocalStore,
) -> CompiledPattern {
    match pat {
        Pattern::Int { value, .. } => {
            // Assumes the value is on the stack
            let value = integer::parse(value);
            CompiledPattern {
                checks: vec![Check::IntegerEquality {
                    local: subject,
                    value,
                }],
                assignments: vec![],
                nested: vec![],
            }
        }
        Pattern::Float { value, .. } => {
            let value = parse_float(value);
            CompiledPattern {
                checks: vec![Check::FloatEquality {
                    local: subject,
                    value,
                }],
                assignments: vec![],
                nested: vec![],
            }
        }
        Pattern::Variable { type_, name, .. } => {
            let local_id = locals.new_id();
            locals.insert(
                local_id,
                Local {
                    id: local_id,
                    name: name.clone(),
                    wasm_type: WasmTypeImpl::from_gleam_type(Arc::clone(&type_), env, table),
                },
            );

            CompiledPattern {
                checks: vec![],
                assignments: vec![Assignment::Named {
                    name: name.clone(),
                    subject_local: subject,
                    target_local: local_id,
                }],
                nested: vec![],
            }
        }
        Pattern::Assign { name, pattern, .. } => {
            let local_id = locals.new_id();
            locals.insert(
                local_id,
                Local {
                    id: local_id,
                    name: name.clone(),
                    wasm_type: WasmTypeImpl::from_gleam_type(pattern.type_(), env, table),
                },
            );

            let cp = compile_pattern(subject, pattern, table, env, strings, locals);
            CompiledPattern {
                checks: vec![],
                assignments: vec![Assignment::Named {
                    name: name.clone(),
                    subject_local: subject,
                    target_local: local_id,
                }],
                nested: vec![cp],
            }
        }
        Pattern::Discard { .. } => CompiledPattern {
            checks: vec![],
            assignments: vec![],
            nested: vec![],
        },

        Pattern::Constructor {
            type_,
            constructor: Inferred::Known(PatternConstructor { name, .. }),
            ..
        } if type_.is_bool() && name == "True" => CompiledPattern {
            checks: vec![Check::BooleanEquality {
                local: subject,
                value: true,
            }],
            assignments: vec![],
            nested: vec![],
        },

        Pattern::Constructor {
            type_,
            constructor: Inferred::Known(PatternConstructor { name, .. }),
            ..
        } if type_.is_bool() && name == "False" => CompiledPattern {
            checks: vec![Check::BooleanEquality {
                local: subject,
                value: false,
            }],
            assignments: vec![],
            nested: vec![],
        },

        Pattern::Constructor {
            type_,
            constructor: Inferred::Known(PatternConstructor { .. }),
            ..
        } if type_.is_nil() => CompiledPattern {
            checks: vec![],
            assignments: vec![],
            nested: vec![],
        },

        Pattern::Constructor {
            constructor:
                Inferred::Known(PatternConstructor {
                    field_map,
                    name: record_name,
                    ..
                }),
            arguments,
            name,
            module,
            ..
        } => {
            if module.is_some() {
                todo!("Constructor access with module name not implemented yet")
            }

            // get product type
            // todo: Nil, True and False
            let product = if let Some(Binding::Product(id)) = env.get(&record_name) {
                table.products.get(id).unwrap()
            } else {
                unreachable!("Invalid product type: {}", record_name)
            };

            let sum = table.sums.get(product.parent).unwrap();

            let product_type = table.types.get(product.type_).unwrap();

            // emit discriminant check
            let checks = vec![Check::ProductEquality {
                subject,
                test_sum: sum.id,
                discriminant: product.tag,
            }];

            // if success, create a new local for the cast subject
            let cast_local_id = locals.new_id();
            locals.insert(
                cast_local_id,
                Local {
                    id: cast_local_id,
                    name: name.clone(),
                    wasm_type: WasmTypeImpl::StructRef(product_type.definition.id),
                },
            );

            let mut assignments = vec![Assignment::Cast {
                subject_local: subject,
                target_local: cast_local_id,
                target_type: product_type.id,
            }];

            // chain remaining patterns
            let mut nested_patterns = vec![];
            for (i, arg) in arguments.iter().enumerate() {
                let field_index = match field_map {
                    None => i,
                    Some(FieldMap { fields, .. }) => {
                        let find = |(key, &val)| {
                            if val as usize == i {
                                Some(key)
                            } else {
                                None
                            }
                        };
                        let label = fields.iter().find_map(find);
                        match label {
                            Some(label) => {
                                // the field is the one with this name
                                product
                                    .fields
                                    .iter()
                                    .position(|f| &f.name == label)
                                    .unwrap()
                            }
                            None => i,
                        }
                    }
                };
                let field = &product.fields[field_index];

                // create a local for the argument
                let arg_variable = locals.new_id();
                locals.insert(
                    arg_variable,
                    Local {
                        id: arg_variable,
                        name: field.name.clone(),
                        wasm_type: field.type_.to_wasm_type(table),
                    },
                );

                let actual_field_index = product
                    .gleam_to_canonical_id
                    .get(&field_index)
                    .copied()
                    .unwrap_or(field_index);

                // assign the argument to the new variable
                assignments.push(Assignment::StructField {
                    subject_local: cast_local_id,
                    target_local: arg_variable,
                    field_index: actual_field_index as u32 + 1,
                    struct_type: product.type_,
                });

                // recursively compile
                let inner_compiled_pattern =
                    compile_pattern(arg_variable, &arg.value, table, env, strings, locals);

                nested_patterns.push(inner_compiled_pattern);
            }

            CompiledPattern {
                checks,
                assignments,
                nested: nested_patterns,
            }
        }
        Pattern::Constructor {
            constructor: Inferred::Unknown,
            ..
        } => unreachable!("Generating code for uninferred type"),
        Pattern::String { value, .. } => CompiledPattern {
            checks: vec![Check::StringEquality {
                local: subject,
                string: unescape(value).into(),
            }],
            assignments: vec![],
            nested: vec![],
        },
        Pattern::StringPrefix {
            left_side_assignment,
            left_side_string,
            right_side_assignment,
            ..
        } => {
            // "Oioi" as x <> rest
            // left_side_string = "Oioi"
            // left_side_assignment = Some(("x", _))
            // right_side_assignment = AssignName::Named("rest")

            // "Oioi" <> _wow
            // left_side_string = "Oioi"
            // left_side_assignment = None
            // right_side_assignment = AssignName::Discard("_wow")

            let left_side_string = unescape(&left_side_string);

            let mut assignments = vec![];

            if let Some((name, _)) = left_side_assignment {
                let string_type_id = table
                    .types
                    .get(table.string_type.unwrap())
                    .unwrap()
                    .definition
                    .id;

                let target_id = locals.new_id();
                locals.insert(
                    target_id,
                    Local {
                        id: target_id,
                        name: name.clone(),
                        wasm_type: WasmTypeImpl::ArrayRef(string_type_id),
                    },
                );

                assignments.push(Assignment::StringConstant {
                    constant: left_side_string.clone().into(),
                    target_local: target_id,
                    name: name.clone(),
                });
            }

            if let Some(name) = right_side_assignment.assigned_name() {
                let string_type_id = table
                    .types
                    .get(table.string_type.unwrap())
                    .unwrap()
                    .definition
                    .id;

                let target_id = locals.new_id();
                locals.insert(
                    target_id,
                    Local {
                        id: target_id,
                        name: name.into(),
                        wasm_type: WasmTypeImpl::ArrayRef(string_type_id),
                    },
                );

                assignments.push(Assignment::StringSuffix {
                    subject_local: subject,
                    target_local: target_id,
                    from: left_side_string.len() as u32,
                    name: name.into(),
                });
            }
            CompiledPattern {
                checks: vec![Check::PrefixEquality {
                    local: subject,
                    prefix: left_side_string.into(),
                }],
                assignments,
                nested: vec![],
            }
        }
        Pattern::BitArray { .. } => todo!("BitArrays not implemented yet"),
        Pattern::VarUsage { .. } => todo!("BitArrays not implemented yet"),
        Pattern::List { .. } => todo!("Lists not implemented yet"),
        Pattern::Tuple { .. } => todo!("Tuples not implemented yet"),
        Pattern::Invalid { .. } => unreachable!("Invalid pattern"),
    }
}

type Instructions = Vec<Instruction<'static>>;

pub struct TranslatedPattern {
    pub condition: Instructions,
    pub assignments: Instructions,
    pub bindings: Vec<(EcoString, LocalId)>,
    pub nested: Vec<TranslatedPattern>,
}

pub fn translate_pattern(
    compiled: CompiledPattern,
    locals: &LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> TranslatedPattern {
    // checks
    let mut cond_expr = vec![];

    if compiled.checks.is_empty() {
        // trivial accept
        cond_expr.push(Instruction::I32Const(1));
    } else {
        // first, concatenate all checks with ands
        let mut first = true;
        for check in compiled.checks {
            match check {
                Check::IntegerEquality { local, value } => {
                    cond_expr.push(Instruction::I32Const(value));
                    cond_expr.push(Instruction::LocalGet(locals.get(local).unwrap().id.id()));
                    cond_expr.push(Instruction::I32Eq);
                }
                Check::FloatEquality { local, value } => {
                    cond_expr.push(Instruction::F64Const(value));
                    cond_expr.push(Instruction::LocalGet(locals.get(local).unwrap().id.id()));
                    cond_expr.push(Instruction::F64Eq);
                }
                Check::ProductEquality {
                    subject,
                    test_sum,
                    discriminant,
                } => {
                    // get type info
                    let sum_type_index = if let Some(sum) = table.sums.get(test_sum) {
                        let type_ = table.types.get(sum.type_).unwrap();
                        type_.definition.id
                    } else {
                        unreachable!("Expected product type to exist")
                    };

                    // push subject on stack
                    cond_expr.push(Instruction::LocalGet(locals.get(subject).unwrap().id.id()));
                    // push discriminant on stack
                    cond_expr.push(Instruction::StructGet {
                        struct_type_index: sum_type_index,
                        field_index: 0,
                    });
                    // push comparison
                    cond_expr.push(Instruction::I32Const(discriminant as i32));
                    cond_expr.push(Instruction::I32Eq);
                }
                Check::BooleanEquality { local, value } => {
                    cond_expr.push(Instruction::I32Const(if value { 1 } else { 0 }));
                    cond_expr.push(Instruction::LocalGet(locals.get(local).unwrap().id.id()));
                    cond_expr.push(Instruction::I32Eq);
                }
                Check::StringEquality { local, string } => {
                    let string_type_id = table
                        .types
                        .get(table.string_type.unwrap())
                        .unwrap()
                        .definition
                        .id;

                    let string_data_id = strings.get_or_insert_data_segment(&string);

                    cond_expr.push(Instruction::LocalGet(local.id()));
                    // offset
                    cond_expr.push(Instruction::I32Const(0));
                    // number of bytes
                    cond_expr.push(Instruction::I32Const(string.len() as _));
                    cond_expr.push(Instruction::ArrayNewData {
                        array_type_index: string_type_id,
                        array_data_index: string_data_id,
                    });
                    cond_expr.push(Instruction::Call(table.string_equality_test.unwrap().id()));
                }
                Check::PrefixEquality { local, prefix } => {
                    let string_type_id = table
                        .types
                        .get(table.string_type.unwrap())
                        .unwrap()
                        .definition
                        .id;

                    let prefix_data = strings.get_or_insert_data_segment(&prefix);

                    // to verify: first we create a substring of the subject, then we compare it with the prefix
                    cond_expr.push(Instruction::LocalGet(local.id()));
                    cond_expr.push(Instruction::I32Const(0));
                    cond_expr.push(Instruction::I32Const(prefix.len() as _));
                    cond_expr.push(Instruction::Call(table.string_substring.unwrap().id()));

                    // offset
                    cond_expr.push(Instruction::I32Const(0));
                    // number of bytes
                    cond_expr.push(Instruction::I32Const(prefix.len() as _));
                    cond_expr.push(Instruction::ArrayNewData {
                        array_type_index: string_type_id,
                        array_data_index: prefix_data,
                    });

                    cond_expr.push(Instruction::Call(table.string_equality_test.unwrap().id()));
                }
            }
            if first {
                first = false;
            } else {
                cond_expr.push(Instruction::I32And);
            }
        }
    }

    // assignments
    let mut assign_expr = vec![];
    let mut bindings = vec![];
    for assignment in compiled.assignments.into_iter() {
        match assignment {
            Assignment::Named {
                subject_local,
                target_local,
                name,
            } => {
                assign_expr.push(Instruction::LocalGet(
                    locals.get(subject_local).unwrap().id.id(),
                ));
                assign_expr.push(Instruction::LocalSet(
                    locals.get(target_local).unwrap().id.id(),
                ));
                bindings.push((name.clone(), target_local));
            }
            Assignment::Cast {
                subject_local,
                target_local,
                target_type,
            } => {
                assign_expr.push(Instruction::LocalGet(
                    locals.get(subject_local).unwrap().id.id(),
                ));
                // CAST!
                assign_expr.push(Instruction::RefCastNonNull(
                    wasm_encoder::HeapType::Concrete(
                        table.types.get(target_type).unwrap().definition.id,
                    ),
                ));
                assign_expr.push(Instruction::LocalSet(
                    locals.get(target_local).unwrap().id.id(),
                ));
            }
            Assignment::StructField {
                subject_local,
                target_local,
                field_index,
                struct_type,
            } => {
                let struct_type_index = if let Some(type_) = table.types.get(struct_type) {
                    type_.definition.id
                } else {
                    unreachable!("Expected struct type to exist")
                };

                assign_expr.push(Instruction::LocalGet(
                    locals.get(subject_local).unwrap().id.id(),
                ));
                assign_expr.push(Instruction::StructGet {
                    struct_type_index,
                    field_index,
                });
                assign_expr.push(Instruction::LocalSet(
                    locals.get(target_local).unwrap().id.id(),
                ));
            }
            Assignment::StringSuffix {
                subject_local,
                target_local,
                from,
                name,
            } => {
                assign_expr.push(Instruction::LocalGet(
                    locals.get(subject_local).unwrap().id.id(),
                ));
                assign_expr.push(Instruction::I32Const(from as _));
                assign_expr.push(Instruction::I32Const(-1));
                assign_expr.push(Instruction::Call(table.string_substring.unwrap().id()));
                assign_expr.push(Instruction::LocalSet(
                    locals.get(target_local).unwrap().id.id(),
                ));

                bindings.push((name.clone(), target_local));
            }
            Assignment::StringConstant {
                constant,
                target_local,
                name,
            } => {
                let string_type_id = table
                    .types
                    .get(table.string_type.unwrap())
                    .unwrap()
                    .definition
                    .id;

                let string_data_id = strings.get_or_insert_data_segment(&constant);

                // offset
                assign_expr.push(Instruction::I32Const(0));
                // number of bytes
                assign_expr.push(Instruction::I32Const(constant.len() as _));
                assign_expr.push(Instruction::ArrayNewData {
                    array_type_index: string_type_id,
                    array_data_index: string_data_id,
                });
                assign_expr.push(Instruction::LocalSet(target_local.id()));
                bindings.push((name.clone(), target_local));
            }
        }
    }

    TranslatedPattern {
        condition: cond_expr,
        assignments: assign_expr,
        bindings,
        nested: compiled
            .nested
            .into_iter()
            .map(|cp| translate_pattern(cp, locals, strings, table))
            .collect(),
    }
}
