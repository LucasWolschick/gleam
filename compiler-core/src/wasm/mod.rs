#![allow(clippy::todo)]

mod encoder;
mod environment;
mod integer;
mod pattern;
mod string;
mod table;

use std::{collections::VecDeque, sync::Arc};

use ecow::EcoString;
use encoder::{
    WasmFunction, WasmGlobal, WasmInstructions, WasmModule, WasmString, WasmType,
    WasmTypeDefinition, WasmTypeImpl,
};
use environment::{Binding, BuiltinType, Environment, TypeBinding};
use itertools::Itertools;
use table::{FieldType, GleamString, Local, LocalStore, Strings, SymbolTable};

use crate::{
    ast::{
        BinOp, ClauseGuard, Statement, TypedAssignment, TypedClause, TypedClauseGuard,
        TypedConstant, TypedExpr, TypedFunction, TypedModule, TypedRecordConstructor,
        TypedStatement,
    },
    io::FileSystemWriter,
    type_::{Type, ValueConstructor, ValueConstructorVariant},
};

pub fn module(writer: &impl FileSystemWriter, ast: &TypedModule) {
    dbg!(&ast);
    let module = construct_module(ast);
    let bytes = encoder::emit(module);
    writer.write_bytes("out.wasm".into(), &bytes[..]).unwrap();
}

fn construct_module(ast: &TypedModule) -> WasmModule {
    use crate::ast::TypedDefinition;

    let mut table = SymbolTable::new();

    let mut root_environment = Environment::new();

    let mut strings = Strings::new();

    let mut functions = vec![];
    let mut constants = vec![];

    // generate prelude types
    let mut module = generate_prelude_types(&mut table, &mut root_environment);

    // FIRST PASS: generate indices for all names
    for definition in &ast.definitions {
        match definition {
            TypedDefinition::CustomType(t) => {
                let sum_type_id = table.types.new_id();
                let sum_type_name: EcoString = format!("sum@{}", t.name).into();
                let sum_type = table::Type {
                    id: sum_type_id,
                    name: sum_type_name.clone(),
                    definition: WasmType {
                        id: sum_type_id.id(),
                        name: sum_type_name,
                        definition: WasmTypeDefinition::Sum,
                    },
                };
                table.types.insert(sum_type_id, sum_type);

                // generate function in second pass. we need the id now
                let equality_function_id = table.functions.new_id();

                let sum_id = table.sums.new_id();
                table.sums.insert(
                    sum_id,
                    table::Sum {
                        id: sum_id,
                        name: t.name.clone(),
                        type_: sum_type_id,
                        public: t.publicity.is_public(),
                        equality_test: equality_function_id,
                    },
                );
                root_environment.set_type(t.name.clone(), TypeBinding::Sum(sum_id));
            }
            TypedDefinition::Function(f) => {
                let function_id = table.functions.new_id();
                root_environment.set(f.name.clone(), Binding::Function(function_id));
            }
            TypedDefinition::ModuleConstant(m) => {
                let constant_id = table.constants.new_id();
                root_environment.set(m.name.clone(), Binding::Constant(constant_id));
            }
            TypedDefinition::Import(_) => todo!("Imports aren't implemented yet"),
            TypedDefinition::TypeAlias(_) => todo!("Type aliases aren't implemented yet"),
        }
    }

    // SECOND PASS: generate the types
    for definition in &ast.definitions {
        match definition {
            TypedDefinition::Function(f) => {
                let function_id = match root_environment.get(&f.name) {
                    Some(Binding::Function(id)) => id,
                    _ => unreachable!("Expected function binding in environment"),
                };

                let function_type_id = table.types.new_id();
                let function_type_name: EcoString = format!("fun@{}", f.name).into();
                let function_type = table::Type {
                    id: function_type_id,
                    name: function_type_name.clone(),
                    definition: WasmType::from_function(
                        f,
                        &function_type_name,
                        function_type_id.id(),
                        &table,
                        &root_environment,
                    ),
                };
                table.types.insert(function_type_id, function_type);

                let function = table::Function {
                    id: function_id,
                    signature: function_type_id,
                    name: f.name.clone(),
                    arity: f.arguments.len() as u32,
                };
                table.functions.insert(function_id, function);

                root_environment.set(f.name.clone(), Binding::Function(function_id));
            }
            TypedDefinition::CustomType(t) => {
                if !t.parameters.is_empty() {
                    todo!("Only concrete, non-generic types");
                }

                let sum_id = match root_environment.get_type(&t.name) {
                    Some(TypeBinding::Sum(id)) => id,
                    _ => panic!("Expected sum binding in environment"),
                };

                let sum_type = table.sums.get(sum_id).expect("Sum type to be added in");
                let sum_type_id = sum_type.type_;

                // add sum type to environment
                root_environment.set_type(t.name.clone(), TypeBinding::Sum(sum_id));

                let mut product_ids = vec![];
                for (tag, variant) in t.constructors.iter().enumerate() {
                    // type
                    let product_type_id = table.types.new_id();
                    let product_type_name: EcoString =
                        format!("typ@{}.{}", t.name, variant.name).into();
                    let product_type = table::Type {
                        id: product_type_id,
                        name: product_type_name.clone(),
                        definition: WasmType::from_product_type(
                            variant,
                            &product_type_name,
                            product_type_id.id(),
                            tag as u32,
                            sum_type_id.id(),
                            &table,
                            &root_environment,
                        ),
                    };
                    table.types.insert(product_type_id, product_type);

                    // constructor signature
                    let constructor_sig_id = table.types.new_id();
                    let constructor_sig_name: EcoString =
                        format!("new@{}.{}", t.name, variant.name).into();
                    let constructor_sig = table::Type {
                        id: constructor_sig_id,
                        name: constructor_sig_name.clone(),
                        definition: WasmType::from_product_type_constructor(
                            variant,
                            &constructor_sig_name,
                            product_type_id.id(),
                            constructor_sig_id.id(),
                            &table,
                            &root_environment,
                        ),
                    };
                    table.types.insert(constructor_sig_id, constructor_sig);

                    // constructor
                    let constructor_id = table.functions.new_id();
                    let constructor = table::Function {
                        id: constructor_id,
                        signature: constructor_sig_id,
                        name: variant.name.clone(),
                        arity: variant.arguments.len() as u32,
                    };
                    table.functions.insert(constructor_id, constructor);

                    // product
                    let product_id = table.products.new_id();

                    let product = if variant.arguments.is_empty() {
                        let global_name = format!("global@{}.{}", t.name, variant.name);

                        // add a global to the symbol table
                        let global_id = table.constants.new_id();
                        let global = table::Constant {
                            id: global_id,
                            name: global_name.clone().into(),
                        };
                        table.constants.insert(global_id, global);

                        // add global
                        constants.push(WasmGlobal {
                            name: global_name.into(),
                            type_: WasmTypeImpl::StructRef(product_type_id.id()),
                            global_index: global_id.id(),
                            initializer: WasmInstructions::single(wasm_encoder::Instruction::Call(
                                constructor_id.id(),
                            )),
                        });

                        table::Product {
                            id: product_id,
                            name: format!("product@{}.{}", t.name, variant.name).into(),
                            type_: product_type_id,
                            parent: sum_id,
                            tag: tag as u32,
                            constructor: constructor_id,
                            kind: table::ProductKind::Simple {
                                instance: global_id,
                            },
                            fields: vec![],
                        }
                    } else {
                        // add constructor to the environment
                        let mut fields = vec![];

                        for (i, arg) in variant.arguments.iter().enumerate() {
                            let label = if arg.label.is_none() {
                                format!("arg{}", i).into()
                            } else {
                                arg.label.as_ref().unwrap().clone()
                            };

                            fields.push(table::ProductField {
                                name: label,
                                index: i,
                                type_: FieldType::from_gleam_type(
                                    Arc::clone(&arg.type_),
                                    &root_environment,
                                    &table,
                                ),
                            });
                        }

                        table::Product {
                            id: product_id,
                            name: format!("product@{}.{}", t.name, variant.name).into(),
                            type_: product_type_id,
                            parent: sum_id,
                            tag: tag as u32,
                            constructor: constructor_id,
                            kind: table::ProductKind::Composite,
                            fields,
                        }
                    };
                    table.products.insert(product_id, product);
                    product_ids.push(product_id);

                    root_environment.set(variant.name.clone(), Binding::Product(product_id));
                }

                // generate equality types
                let equality_test_id = table.types.new_id();
                let equality_test_name: EcoString = format!("eq@{}", t.name).into();
                let equality_test = table::Type {
                    id: equality_test_id,
                    name: equality_test_name.clone(),
                    definition: WasmType {
                        id: equality_test_id.id(),
                        name: equality_test_name,
                        definition: WasmTypeDefinition::Function {
                            parameters: vec![
                                WasmTypeImpl::StructRef(sum_type_id.id()),
                                WasmTypeImpl::StructRef(sum_type_id.id()),
                            ],
                            returns: WasmTypeImpl::Bool,
                        },
                    },
                };
                table.types.insert(equality_test_id, equality_test);

                // generate equality function
                let equality_function_id = sum_type.equality_test;
                let equality_function = table::Function {
                    id: equality_function_id,
                    signature: equality_test_id,
                    name: format!("eq@{}", t.name).into(),
                    arity: 2,
                };
                table
                    .functions
                    .insert(equality_function_id, equality_function);
            }
            TypedDefinition::ModuleConstant(_) => {
                // we assign the constant type in the last pass
            }
            TypedDefinition::TypeAlias(_) => todo!("Type aliases aren't implemented yet"),
            TypedDefinition::Import(_) => todo!("Imports aren't implemented yet"),
        }
    }

    // THIRD PASS: generate the actual function bodies and types
    for definition in &ast.definitions {
        match definition {
            TypedDefinition::Function(f) => {
                let function_id = root_environment.get(&f.name).unwrap();
                match function_id {
                    Binding::Function(id) => {
                        let function_data = table.functions.get(id).unwrap();
                        let function = emit_function(
                            f,
                            function_data.id,
                            &table,
                            &mut strings,
                            &root_environment,
                        );
                        functions.push(function);
                    }
                    _ => unreachable!("Expected function binding in environment"),
                }
            }
            TypedDefinition::CustomType(c) => {
                // generate the type constructors
                for variant in &c.constructors {
                    let product_id = root_environment.get(&variant.name).unwrap();
                    match product_id {
                        Binding::Product(id) => {
                            let table_product = table.products.get(id).unwrap();
                            let table_sum = table.sums.get(table_product.parent).unwrap();
                            let function = emit_variant_constructor(
                                variant,
                                table_product,
                                &table,
                                table_sum.public,
                            );
                            functions.push(function);
                        }
                        _ => unreachable!("Expected product binding in environment"),
                    }
                }
                // generate the equality function
                let sum_id = root_environment.get_type(&c.name).unwrap();
                match sum_id {
                    TypeBinding::Sum(id) => {
                        let sum = table.sums.get(id).unwrap();
                        let function = emit_sum_equality(sum, &table);
                        functions.push(function);
                    }
                }
            }
            TypedDefinition::ModuleConstant(m) => {
                let constant_id = match root_environment.get(&m.name) {
                    Some(Binding::Constant(id)) => id,
                    _ => unreachable!("Expected constant binding in environment"),
                };

                table.constants.insert(
                    constant_id,
                    table::Constant {
                        id: constant_id,
                        name: m.name.clone(),
                    },
                );

                constants.push(WasmGlobal {
                    name: m.name.clone(),
                    global_index: constant_id.id(),
                    type_: WasmTypeImpl::from_gleam_type(
                        Arc::clone(&m.type_),
                        &root_environment,
                        &table,
                    ),
                    initializer: emit_constant(m.value.as_ref(), &root_environment, &table),
                })
            }
            TypedDefinition::TypeAlias(_) => todo!("Type aliases aren't implemented yet"),
            TypedDefinition::Import(_) => todo!("Imports aren't implemented yet"),
        }
    }

    module.functions.extend(functions);
    module.constants.extend(constants);
    module
        .strings
        .extend(strings.as_list().into_iter().map(|x| WasmString {
            data_index: x.data_segment,
            value: x.value.clone(),
        }));
    module
        .types
        .extend(table.types.as_list().into_iter().map(|x| x.definition));

    module
}

fn emit_sum_equality(sum: &table::Sum, table: &SymbolTable) -> WasmFunction {
    use wasm_encoder::Instruction as Inst;

    let mut instructions = vec![];

    let struct_type = table.types.get(sum.type_).unwrap();
    let function = table.functions.get(sum.equality_test).unwrap();
    let function_type = table.types.get(function.signature).unwrap();

    let mut locals = LocalStore::new();

    // outer block
    instructions.push(Inst::Block(wasm_encoder::BlockType::Empty));

    // get the tag of the first argument
    instructions.push(Inst::LocalGet(0));
    instructions.push(Inst::StructGet {
        struct_type_index: struct_type.definition.id,
        field_index: 0,
    });

    // get the tag of the second argument
    instructions.push(Inst::LocalGet(1));
    instructions.push(Inst::StructGet {
        struct_type_index: struct_type.definition.id,
        field_index: 0,
    });

    // compare the tags
    instructions.push(Inst::I32Eq);
    instructions.push(Inst::I32Eqz);
    instructions.push(Inst::BrIf(0)); // return false

    // generate comparison code for each variant
    let variants = table
        .products
        .as_list()
        .into_iter()
        .filter(|p| p.parent == sum.id)
        .collect_vec();

    for variant in variants {
        // start block
        instructions.push(Inst::Block(wasm_encoder::BlockType::Empty));

        // compare tag
        instructions.push(Inst::LocalGet(0));
        instructions.push(Inst::StructGet {
            struct_type_index: struct_type.definition.id,
            field_index: 0,
        });
        instructions.push(Inst::I32Const(variant.tag as _));
        instructions.push(Inst::I32Eq);
        instructions.push(Inst::I32Eqz);
        instructions.push(Inst::BrIf(0)); // next variant

        // create local storing casted struct
        let struct_type = table.types.get(variant.type_).unwrap();
        let lhs_local = locals.new_id();
        let rhs_local = locals.new_id();
        locals.insert(
            lhs_local,
            Local {
                id: lhs_local,
                name: format!("lhs@{}", variant.name).into(),
                wasm_type: WasmTypeImpl::StructRef(struct_type.definition.id),
            },
        );
        locals.insert(
            rhs_local,
            Local {
                id: rhs_local,
                name: format!("rhs@{}", variant.name).into(),
                wasm_type: WasmTypeImpl::StructRef(struct_type.definition.id),
            },
        );

        // cast the structs
        instructions.push(Inst::LocalGet(0));
        instructions.push(Inst::RefCastNonNull(wasm_encoder::HeapType::Concrete(
            struct_type.definition.id,
        )));
        instructions.push(Inst::LocalSet(2 + lhs_local.id()));

        instructions.push(Inst::LocalGet(1));
        instructions.push(Inst::RefCastNonNull(wasm_encoder::HeapType::Concrete(
            struct_type.definition.id,
        )));
        instructions.push(Inst::LocalSet(2 + rhs_local.id()));

        // for each field, compare the values
        for field in &variant.fields {
            // start block
            instructions.push(Inst::Block(wasm_encoder::BlockType::Empty));

            // get the field from the first struct
            instructions.push(Inst::LocalGet(2 + lhs_local.id()));
            instructions.push(Inst::StructGet {
                struct_type_index: struct_type.definition.id,
                field_index: field.index as u32 + 1,
            });

            // get the field from the second struct
            instructions.push(Inst::LocalGet(2 + rhs_local.id()));
            instructions.push(Inst::StructGet {
                struct_type_index: struct_type.definition.id,
                field_index: field.index as u32 + 1,
            });

            // generate the appropriate equality test
            instructions.extend(emit_equality_test(&field.type_, table).lst);

            // if the test fails, return false
            instructions.push(Inst::I32Eqz);
            instructions.push(Inst::BrIf(2)); // field, variant, function

            // end block
            instructions.push(Inst::End);
        }

        // unreachable
        instructions.push(Inst::Unreachable);

        // end block
        instructions.push(Inst::End);
    }

    // return true if we got here
    instructions.push(Inst::I32Const(1));
    instructions.push(Inst::Return);

    // end outer block
    instructions.push(Inst::End);

    instructions.push(Inst::I32Const(0)); // return false

    // finish function
    instructions.push(Inst::End);

    WasmFunction {
        name: format!("eq@{}", sum.name).into(),
        type_index: function_type.definition.id,
        instructions: WasmInstructions { lst: instructions },
        locals: locals
            .as_list()
            .into_iter()
            .map(|local| (local.name, local.wasm_type))
            .collect_vec(),
        argument_names: vec![Some(EcoString::from("lhs")), Some(EcoString::from("rhs"))],
        function_index: function.id.id(),
        arity: 2,
        public: false,
    }
}

fn emit_equality_test(type_: &FieldType, table: &SymbolTable) -> WasmInstructions {
    // assumes that there are two values on the stack (lhs, rhs)

    match type_ {
        FieldType::Sum(id) => {
            let sum = table.sums.get(*id).unwrap();
            let function = table.functions.get(sum.equality_test).unwrap();
            WasmInstructions::single(wasm_encoder::Instruction::Call(function.id.id()))
        }
        FieldType::Int => integer::eq(),
        FieldType::Float => WasmInstructions::single(wasm_encoder::Instruction::F64Eq),
        FieldType::Bool | FieldType::Nil => {
            WasmInstructions::single(wasm_encoder::Instruction::I32Eq)
        }
        FieldType::String => WasmInstructions::single(wasm_encoder::Instruction::Call(
            table.string_equality_test.unwrap().id(),
        )),
    }
}

fn emit_constant(
    value: &TypedConstant,
    root_environment: &Environment<'_>,
    table: &SymbolTable,
) -> WasmInstructions {
    match value {
        TypedConstant::Int { value, .. } => {
            let val = integer::parse(value);
            integer::const_(val)
        }
        TypedConstant::Float { value, .. } => {
            let val = parse_float(value);
            WasmInstructions::single(wasm_encoder::Instruction::F64Const(val))
        }
        TypedConstant::Var { .. } => todo!("Variable constants not implemented yet"),
        TypedConstant::Record { .. } => todo!("Record constants not implemented yet"),
        TypedConstant::String { .. } => todo!("Strings not implemented yet"),
        TypedConstant::Tuple { .. } => todo!("Tuples not implemented yet"),
        TypedConstant::List { .. } => todo!("Lists not implemented yet"),
        TypedConstant::BitArray { .. } => todo!("BitArrays not implemented yet"),
        TypedConstant::Invalid { .. } => unreachable!(),
    }
}

fn generate_prelude_types(table: &mut SymbolTable, env: &mut Environment<'_>) -> WasmModule {
    // etc
    let mut module = WasmModule {
        functions: vec![],
        constants: vec![],
        strings: vec![],
        types: vec![],
    };

    // Implement division signature
    // - PreludeType::Float
    let float_div_type_id = table.types.new_id();
    table.types.insert(
        float_div_type_id,
        table::Type {
            id: float_div_type_id,
            name: "@Float@div".into(),
            definition: WasmType {
                name: "@Float@div".into(),
                id: float_div_type_id.id(),
                definition: WasmTypeDefinition::Function {
                    parameters: vec![WasmTypeImpl::Float],
                    returns: WasmTypeImpl::Float,
                },
            },
        },
    );
    table.float_division = Some(float_div_type_id);

    // - PreludeType::Int
    let int_div_type_id = table.types.new_id();
    table.types.insert(
        int_div_type_id,
        table::Type {
            id: int_div_type_id,
            name: "@Int@div".into(),
            definition: WasmType {
                name: "@Int@div".into(),
                id: int_div_type_id.id(),
                definition: WasmTypeDefinition::Function {
                    parameters: vec![WasmTypeImpl::Int],
                    returns: WasmTypeImpl::Int,
                },
            },
        },
    );
    table.int_division = Some(int_div_type_id);

    // - PreludeType::Nil
    env.set("Nil".into(), Binding::Builtin(BuiltinType::Nil));

    // - PreludeType::Bool
    env.set(
        "True".into(),
        Binding::Builtin(BuiltinType::Boolean { value: true }),
    );
    env.set(
        "False".into(),
        Binding::Builtin(BuiltinType::Boolean { value: false }),
    );

    // - PreludeType::String
    let string_type_id = table.types.new_id();
    table.types.insert(
        string_type_id,
        table::Type {
            id: string_type_id,
            name: "String".into(),
            definition: WasmType {
                name: "String".into(),
                id: string_type_id.id(),
                definition: WasmTypeDefinition::String,
            },
        },
    );
    table.string_type = Some(string_type_id);

    // also generate the string function
    let string_type = table
        .types
        .get(table.string_type.unwrap())
        .unwrap()
        .definition
        .id;

    let string_equality_test_type_id = table.types.new_id();
    let string_equality_test_type = table::Type {
        id: string_equality_test_type_id,
        name: "typ@@string_equality".into(),
        definition: WasmType {
            name: "typ@eq@String".into(),
            id: string_equality_test_type_id.id(),
            definition: WasmTypeDefinition::Function {
                parameters: [WasmTypeImpl::ArrayRef(string_type); 2].to_vec(),
                returns: WasmTypeImpl::Bool,
            },
        },
    };
    table
        .types
        .insert(string_equality_test_type_id, string_equality_test_type);

    let string_equality_test_id = table.functions.new_id();
    let string_equality_test = table::Function {
        id: string_equality_test_id,
        signature: string_equality_test_type_id,
        name: "eq@String".into(),
        arity: 2,
    };
    table
        .functions
        .insert(string_equality_test_id, string_equality_test);
    table.string_equality_test = Some(string_equality_test_id);

    let string_fn = string::emit_string_equality_function(
        string_equality_test_type_id,
        string_equality_test_id,
        &table,
    );
    module.functions.push(string_fn);

    // To be implemented:
    // - PreludeType::BitArray
    // TODO: BitArrays

    // - PreludeType::List
    // TODO: Lists

    // - PreludeType::Result
    // TODO: Results

    // - PreludeType::UtfCodepoint
    // TODO: UtfCodepoints

    module
}

fn emit_variant_constructor(
    constructor: &TypedRecordConstructor,
    variant_data: &table::Product,
    table: &SymbolTable,
    public: bool,
) -> WasmFunction {
    let mut instructions = vec![];
    instructions.extend(integer::const_(variant_data.tag as _).lst);
    instructions.extend(
        (0..constructor.arguments.len()).map(|i| wasm_encoder::Instruction::LocalGet(i as u32)),
    );
    instructions.push(wasm_encoder::Instruction::StructNew(
        variant_data.type_.id(),
    ));
    instructions.push(wasm_encoder::Instruction::End);

    let function_index = variant_data.constructor;
    let function = table.functions.get(function_index).unwrap();

    WasmFunction {
        name: format!("new@{}", &function.name).into(),
        function_index: function_index.id(),
        type_index: function.signature.id(),
        instructions: WasmInstructions { lst: instructions },
        argument_names: constructor.arguments.iter().map(|_| None).collect(),
        locals: vec![],
        arity: constructor.arguments.len() as u32,
        public,
    }
}

fn emit_function(
    function: &TypedFunction,
    function_id: table::FunctionId,
    table: &SymbolTable,
    strings: &mut Strings,
    top_level_env: &Environment<'_>,
) -> WasmFunction {
    let mut env = Environment::with_enclosing(top_level_env);
    let mut locals = LocalStore::new();

    let function_data = table
        .functions
        .get(function_id)
        .expect("The function exists");

    for arg in &function.arguments {
        // get a variable number
        let idx = locals.new_id();

        let name = arg
            .names
            .get_variable_name()
            .cloned()
            .unwrap_or_else(|| "#{idx}".into());

        locals.insert(
            idx,
            Local {
                id: idx,
                name: name.clone(),
                wasm_type: WasmTypeImpl::from_gleam_type(Arc::clone(&arg.type_), &env, table),
            },
        );

        // add arguments to the environment
        env.set(name, Binding::Local(idx));
    }

    let mut instructions =
        emit_statement_list(&function.body, &mut env, &mut locals, strings, table);
    instructions.lst.push(wasm_encoder::Instruction::End);

    WasmFunction {
        name: function_data.name.clone(),
        function_index: function_data.id.id(),
        type_index: function_data.signature.id(),
        instructions,
        argument_names: locals
            .as_list()
            .into_iter()
            .take(function_data.arity as _)
            .map(|local| Some(local.name))
            .collect_vec(),
        locals: locals
            .as_list()
            .into_iter()
            .skip(function_data.arity as _)
            .map(|local| (local.name, local.wasm_type))
            .collect_vec(),
        arity: function_data.arity,
        public: function.publicity.is_public(),
    }
}

fn emit_statement_list(
    statements: &[TypedStatement],
    env: &mut Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    let mut instructions = WasmInstructions::empty();

    for statement in statements.iter().dropping_back(1) {
        let new_insts = emit_statement(statement, env, locals, strings, table);
        instructions.lst.extend(new_insts.lst);
        instructions.lst.push(wasm_encoder::Instruction::Drop);
    }
    if let Some(statement) = statements.last() {
        let new_insts = emit_statement(statement, env, locals, strings, table);
        instructions.lst.extend(new_insts.lst);
    }

    instructions
}

fn emit_statement(
    statement: &TypedStatement,
    env: &mut Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    match statement {
        Statement::Expression(expression) => {
            emit_expression(expression, env, locals, strings, table)
        }
        Statement::Assignment(assignment) => {
            emit_assignment(assignment, env, locals, strings, table)
        }
        Statement::Use(_) => {
            unreachable!("Use statements should not be present at this stage of compilation")
        }
    }
}

fn emit_assignment(
    assignment: &TypedAssignment,
    env: &mut Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    // create a new local for the assignment subject
    let id = locals.new_id();
    let type_ = WasmTypeImpl::from_gleam_type(assignment.type_(), env, table);
    let name = format!("#assign#{}", id.id());
    locals.insert(
        id,
        Local {
            id,
            name: name.into(),
            wasm_type: type_,
        },
    );

    // compile pattern
    let compiled = pattern::compile_pattern(id, &assignment.pattern, table, env, locals);
    let translated = pattern::translate_pattern(compiled, locals, table);

    // emit value
    let mut insts = emit_expression(&assignment.value, env, locals, strings, table);
    insts.lst.push(wasm_encoder::Instruction::LocalSet(id.id()));

    if assignment.kind.is_assert() {
        // emit the conditions and assignments in BFS order

        // envolving block
        insts.lst.push(wasm_encoder::Instruction::Block(
            wasm_encoder::BlockType::Empty, // because we don't return anything
        ));

        // pattern block
        insts.lst.push(wasm_encoder::Instruction::Block(
            wasm_encoder::BlockType::Empty,
        ));

        let mut queue = VecDeque::from([translated]);

        while let Some(t) = queue.pop_front() {
            // emit conditions
            insts.lst.extend(t.condition);

            // jump to clause block
            insts.lst.push(wasm_encoder::Instruction::I32Eqz);
            insts.lst.push(wasm_encoder::Instruction::BrIf(0)); // clause

            // emit assignments
            insts.lst.extend(t.assignments);

            // add bindings to the environment
            for (name, local_id) in t.bindings.iter() {
                env.set(name.clone(), Binding::Local(*local_id));
            }

            // enqueue nested patterns
            queue.extend(t.nested);
        }

        // in regular pattern matching, here would be the result of the match expression
        // but we don't need it here since we're only attributing the value to a variable

        // break out of the case
        insts.lst.push(wasm_encoder::Instruction::Br(1)); // case

        // close pattern block
        insts.lst.push(wasm_encoder::Instruction::End);

        // there's no code to execute, so we need to add an unreachable
        // TODO: emit a proper error message
        insts.lst.push(wasm_encoder::Instruction::Unreachable);

        // close envolving block
        insts.lst.push(wasm_encoder::Instruction::End);
    } else {
        // this is irrefutable so do not emit any checks
        let mut queue = VecDeque::from([translated]);

        while let Some(t) = queue.pop_front() {
            // emit assignments
            insts.lst.extend(t.assignments);

            // add bindings to the environment
            for (name, local_id) in t.bindings.iter() {
                env.set(name.clone(), Binding::Local(*local_id));
            }

            // enqueue nested patterns
            queue.extend(t.nested);
        }
    }

    // return the value
    insts.lst.push(wasm_encoder::Instruction::LocalGet(id.id()));

    insts
}

fn emit_expression(
    expression: &TypedExpr,
    env: &Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    match expression {
        TypedExpr::Int { value, .. } => {
            let val = integer::parse(value);
            integer::const_(val)
        }
        TypedExpr::NegateInt { value, .. } => {
            let mut insts = emit_expression(value, env, locals, strings, table);
            insts.lst.extend(integer::const_(-1).lst);
            insts.lst.extend(integer::mul().lst);
            insts
        }
        TypedExpr::Block { statements, .. } => {
            // create new Environment
            let statements = emit_statement_list(
                statements,
                &mut Environment::with_enclosing(env),
                locals,
                strings,
                table,
            );
            statements
        }
        TypedExpr::BinOp {
            typ,
            name,
            left,
            right,
            ..
        } => emit_binary_operation(env, locals, strings, table, typ, *name, left, right),
        TypedExpr::Var {
            constructor, name, ..
        } => emit_value_constructor(constructor, env, name, table),
        TypedExpr::Call { fun, args, .. } => {
            let mut insts = WasmInstructions::empty();
            // TODO: implement out-of-declared-order parameter function calls
            for arg in args {
                let new_insts = emit_expression(&arg.value, env, locals, strings, table);
                insts.lst.extend(new_insts.lst);
            }
            match fun.as_ref() {
                TypedExpr::Var {
                    constructor:
                        ValueConstructor {
                            variant: ValueConstructorVariant::ModuleFn { name, .. },
                            ..
                        },
                    ..
                } => match env.get(name).unwrap() {
                    Binding::Function(id) => {
                        insts.lst.push(wasm_encoder::Instruction::Call(id.id()));
                        insts
                    }
                    _ => todo!("Expected function binding"),
                },
                TypedExpr::Var {
                    constructor:
                        ValueConstructor {
                            variant: ValueConstructorVariant::Record { name, .. },
                            ..
                        },
                    ..
                } => {
                    if let Some(Binding::Product(id)) = env.get(name) {
                        let product = table.products.get(id).unwrap();
                        insts
                            .lst
                            .push(wasm_encoder::Instruction::Call(product.constructor.id()));
                        insts
                    } else {
                        panic!("Expected product binding")
                    }
                }
                _ => todo!("Only simple function calls and type constructors"),
            }
        }
        TypedExpr::Case {
            subjects,
            clauses,
            typ,
            ..
        } => emit_case_expression(
            subjects,
            clauses,
            Arc::clone(typ),
            env,
            locals,
            strings,
            table,
        ),
        TypedExpr::Float { value, .. } => {
            let val = parse_float(value);
            WasmInstructions::single(wasm_encoder::Instruction::F64Const(val))
        }
        TypedExpr::Todo { message, .. } => {
            if message.is_some() {
                todo!("Todo with message not implemented yet");
            }

            WasmInstructions::single(wasm_encoder::Instruction::Unreachable)
        }
        TypedExpr::Panic { message, .. } => {
            if message.is_some() {
                todo!("Panic with message not implemented yet");
            }

            WasmInstructions::single(wasm_encoder::Instruction::Unreachable)
        }
        TypedExpr::String { value, .. } => {
            let string_type_id = table.string_type.unwrap();
            let string_type = table.types.get(string_type_id).unwrap();

            let data_segment = strings.get_or_insert_data_segment(value);
            WasmInstructions {
                lst: vec![
                    // number of bytes
                    wasm_encoder::Instruction::I32Const(value.len() as _),
                    // offset
                    wasm_encoder::Instruction::I32Const(0),
                    wasm_encoder::Instruction::ArrayNewData {
                        array_type_index: string_type.definition.id,
                        array_data_index: data_segment,
                    },
                ],
            }
        }
        TypedExpr::Pipeline { .. } => todo!("Pipelines not implemented yet"),
        TypedExpr::Fn { .. } => todo!("Inner functions not implemented yet"),
        TypedExpr::List { .. } => todo!("Lists not implemented yet"),
        TypedExpr::RecordAccess { .. } => todo!("Record access not implemented yet"),
        TypedExpr::ModuleSelect { .. } => todo!("Module access not implemented yet"),
        TypedExpr::Tuple { .. } => todo!("Tuples not implemented yet"),
        TypedExpr::TupleIndex { .. } => todo!("Tuple index not implemented yet"),
        TypedExpr::BitArray { .. } => todo!("BitArrays not implemented yet"),
        TypedExpr::RecordUpdate { .. } => todo!("Record update not implemented yet"),
        TypedExpr::NegateBool { value, .. } => {
            let mut insts = emit_expression(value, env, locals, strings, table);
            insts.lst.push(wasm_encoder::Instruction::I32Eqz);
            insts
        }
        TypedExpr::Invalid { .. } => unreachable!("Invalid expression"),
    }
}

fn emit_value_constructor(
    constructor: &ValueConstructor,
    env: &Environment<'_>,
    name: &EcoString,
    table: &SymbolTable,
) -> WasmInstructions {
    match &constructor.variant {
        ValueConstructorVariant::LocalVariable { .. } => match env.get(name).unwrap() {
            Binding::Local(id) => {
                WasmInstructions::single(wasm_encoder::Instruction::LocalGet(id.id()))
            }
            _ => todo!("Expected local variable binding"),
        },

        // TODO: handle module
        ValueConstructorVariant::ModuleConstant { module, .. } => {
            // grab the global
            match env.get(&name) {
                Some(Binding::Constant(id)) => WasmInstructions {
                    lst: vec![
                        wasm_encoder::Instruction::GlobalGet(id.id()),
                        wasm_encoder::Instruction::RefAsNonNull,
                    ],
                },
                _ => todo!("Expected constant binding"),
            }
        }

        // TODO: handle module
        // TODO: handle field_map
        ValueConstructorVariant::ModuleFn {
            name,
            module,
            field_map,
            ..
        } => match env.get(name).unwrap() {
            Binding::Function(id) => {
                WasmInstructions::single(wasm_encoder::Instruction::Call(id.id()))
            }

            _ => todo!("Expected function binding"),
        },
        // TODO: handle module
        // TODO: handle field_map
        ValueConstructorVariant::Record {
            name,
            module,
            field_map,
            arity: 0,
            ..
        } => match env.get(name).unwrap() {
            Binding::Product(id) => {
                let product = table.products.get(id).unwrap();
                match product {
                    table::Product {
                        kind: table::ProductKind::Simple { instance },
                        ..
                    } => WasmInstructions {
                        lst: vec![
                            wasm_encoder::Instruction::GlobalGet(instance.id()),
                            wasm_encoder::Instruction::RefAsNonNull, // safe because we initialize all globals before running
                        ],
                    },

                    _ => todo!("Expected simple product"),
                }
            }
            Binding::Builtin(BuiltinType::Nil) => {
                WasmInstructions::single(wasm_encoder::Instruction::I32Const(0))
            }
            Binding::Builtin(BuiltinType::Boolean { value }) => {
                WasmInstructions::single(wasm_encoder::Instruction::I32Const(if value {
                    1
                } else {
                    0
                }))
            }
            _ => todo!("Expected product binding"),
        },
        ValueConstructorVariant::Record { .. } => todo!("Only simple records with 0 fields"),
        ValueConstructorVariant::LocalConstant { literal } => emit_constant(literal, env, table),
    }
}
/*
    A | B | C -> code1
    D -> code2

    block 'case
        block 'clause
            block 'group
                block 'a
                    A checks (fail = break 'a)
                    A attributions
                    break 'group
                end
                block 'b
                    B checks (fail = break 'b)
                    B attributions
                    break 'group
                end
                block 'c
                    C checks (fail = break 'c)
                    C attributions
                    break 'group
                end
                break 'clause
            end
            code1
            break 1
        end
        block
            D checks
            D attributions
            code2
            break 1
        end
        unreachable
    end
*/

fn emit_case_expression(
    subjects: &[TypedExpr],
    clauses: &[TypedClause],
    type_: Arc<Type>,
    env: &Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    // first, declare a new local for every subject
    let ids: Vec<_> = subjects
        .iter()
        .map(|subject| {
            let id = locals.new_id();
            let name = format!("#case#{}", id.id());
            locals.insert(
                id,
                Local {
                    id,
                    name: name.into(),
                    wasm_type: WasmTypeImpl::from_gleam_type(
                        Arc::clone(&subject.type_()),
                        env,
                        table,
                    ),
                },
            );
            id
        })
        .collect();

    // then, emit the subject expressions and store them in the locals
    let mut insts = WasmInstructions::empty();
    for (id, subject) in ids.iter().zip(subjects) {
        let new_insts = emit_expression(subject, env, locals, strings, table);
        insts.lst.extend(new_insts.lst);
        insts.lst.push(wasm_encoder::Instruction::LocalSet(id.id()));
    }

    let result_type = WasmTypeImpl::from_gleam_type(Arc::clone(&type_), env, table);

    // open case block
    insts.lst.push(wasm_encoder::Instruction::Block(
        wasm_encoder::BlockType::Result(result_type.to_val_type()),
    ));

    for clause in clauses {
        // TODO: we just duplicate our code for each alt pattern, but we could use
        //       a smarter approach with blocks
        //
        //       the idea is to use four levels of blocks: case block, clause block,
        //       pattern group block and pattern block
        //        - the case block is composed of a sequence of clause blocks and an
        //          unreachable instruction
        //        - each clause block is composed of a pattern group block, matching
        //          expression code and a break 'case
        //        - a pattern group block is a sequence of pattern blocks ended by a
        //          break 'clause
        //        - each pattern block has all conditions and definitions necessary to
        //          the pattern being compiled. if a pattern doesn't match, it breaks
        //          'pattern. if it does, it breaks 'group.
        //
        //      so why don't we do this? well, Gleam says that in the case that there
        //      exist multiple alternate patterns, the valid bindings set is the intersection
        //      of all bindings across alternates. doing this properly would require
        //      reusing locals, or at least creating a new set of locals and initializing
        //      them with each pattern's attributions.
        let mut patterns = vec![clause.pattern.clone()];
        patterns.extend(clause.alternative_patterns.iter().cloned());

        for clause_pattern in patterns.into_iter() {
            let mut inner_env = Environment::with_enclosing(env);

            // open clause block
            insts.lst.push(wasm_encoder::Instruction::Block(
                wasm_encoder::BlockType::Empty,
            ));

            // TODO: we check multipatterns sequentially, not concurrently
            // this could be more performant
            for (pattern, subject_id) in clause_pattern.iter().zip(&ids) {
                let compiled =
                    pattern::compile_pattern(*subject_id, pattern, table, &inner_env, locals);
                let translated = pattern::translate_pattern(compiled, locals, table);

                // we need to emit the conditions and assignments in tree order
                // (a leaf node's code must show up after the parent node's code)
                // it doesn't actually matter if it's a DFS or BFS, but we're doing BFS here
                // because inner conditions depend on outer conditions
                // (topological ordering)
                let mut queue = VecDeque::from([translated]);

                while let Some(t) = queue.pop_front() {
                    // emit conditions
                    insts.lst.extend(t.condition);

                    // jump to clause block
                    insts.lst.push(wasm_encoder::Instruction::I32Eqz);
                    insts.lst.push(wasm_encoder::Instruction::BrIf(0)); // clause

                    // emit assignments
                    insts.lst.extend(t.assignments);

                    // add bindings to the environment
                    for (name, local_id) in t.bindings.iter() {
                        inner_env.set(name.clone(), Binding::Local(*local_id));
                    }

                    // enqueue nested patterns
                    queue.extend(t.nested);
                }
            }

            // if we have a clause guard, we need to test it here (with the inner binding)
            if let Some(guard) = &clause.guard {
                // emit condition
                insts.lst.extend(
                    emit_clause_guard_expression(guard, &inner_env, locals, strings, table).lst,
                );

                insts.lst.push(wasm_encoder::Instruction::I32Eqz);
                insts.lst.push(wasm_encoder::Instruction::BrIf(0)); // clause
            }

            // emit code
            let new_insts = emit_expression(&clause.then, &inner_env, locals, strings, table);
            insts.lst.extend(new_insts.lst);

            // break out of the case
            insts.lst.push(wasm_encoder::Instruction::Br(1)); // case

            // close clause block
            insts.lst.push(wasm_encoder::Instruction::End);
        }
    }

    // add unreachable (all fine due to exhaustiveness)
    insts.lst.push(wasm_encoder::Instruction::Unreachable);

    // close case block
    insts.lst.push(wasm_encoder::Instruction::End);

    insts.into()
}

fn emit_clause_guard_expression(
    guard: &TypedClauseGuard,
    env: &Environment<'_>,
    locals: &LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
) -> WasmInstructions {
    match guard {
        ClauseGuard::Equals { left, right, .. } => {
            // check types
            assert_eq!(left.type_(), right.type_(), "Expected equal types");

            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(
                emit_equality_test(&FieldType::from_gleam_type(left.type_(), env, table), table)
                    .lst,
            );
            insts
        }
        ClauseGuard::NotEquals { left, right, .. } => {
            // check types
            assert_eq!(left.type_(), right.type_(), "Expected equal types");

            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(
                emit_equality_test(&FieldType::from_gleam_type(left.type_(), env, table), table)
                    .lst,
            );
            insts.lst.push(wasm_encoder::Instruction::I32Eqz);
            insts
        }
        ClauseGuard::LtInt { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::lt().lst);
            insts
        }
        ClauseGuard::LtEqInt { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::lte().lst);
            insts
        }
        ClauseGuard::LtFloat { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Lt);
            insts
        }
        ClauseGuard::LtEqFloat { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Le);
            insts
        }
        ClauseGuard::GtEqInt { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::gte().lst);
            insts
        }
        ClauseGuard::GtInt { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::gt().lst);
            insts
        }
        ClauseGuard::GtEqFloat { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Ge);
            insts
        }
        ClauseGuard::GtFloat { left, right, .. } => {
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);
            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Gt);
            insts
        }
        ClauseGuard::And { left, right, .. } => {
            // short circuiting behavior: if left is false, don't evaluate right
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::Result(WasmTypeImpl::Bool.to_val_type()),
            ));

            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);

            insts.lst.push(wasm_encoder::Instruction::Else);
            insts.lst.push(wasm_encoder::Instruction::I32Const(0));
            insts.lst.push(wasm_encoder::Instruction::End);
            insts
        }
        ClauseGuard::Or { left, right, .. } => {
            // short circuiting behavior: if left is true, don't evaluate right
            let mut insts = emit_clause_guard_expression(left, env, locals, strings, table);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::Result(WasmTypeImpl::Bool.to_val_type()),
            ));
            insts.lst.push(wasm_encoder::Instruction::I32Const(1));
            insts.lst.push(wasm_encoder::Instruction::Else);

            let right_insts = emit_clause_guard_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);

            insts.lst.push(wasm_encoder::Instruction::End);
            insts
        }
        ClauseGuard::Not { expression, .. } => {
            let mut insts = emit_clause_guard_expression(expression, env, locals, strings, table);
            insts.lst.push(wasm_encoder::Instruction::I32Eqz);
            insts
        }
        ClauseGuard::Var { name, .. } => {
            // this is simple variable access!
            match env.get(name) {
                Some(Binding::Builtin(BuiltinType::Boolean { value })) => {
                    WasmInstructions::single(wasm_encoder::Instruction::I32Const(if value {
                        1
                    } else {
                        0
                    }))
                }
                Some(Binding::Builtin(BuiltinType::Nil)) => {
                    WasmInstructions::single(wasm_encoder::Instruction::I32Const(0))
                }
                Some(Binding::Local(id)) => {
                    WasmInstructions::single(wasm_encoder::Instruction::LocalGet(id.id()))
                }
                Some(Binding::Product(id)) => {
                    let product = table.products.get(id).unwrap();
                    match product.kind {
                        table::ProductKind::Simple { instance } => WasmInstructions {
                            lst: vec![
                                wasm_encoder::Instruction::GlobalGet(instance.id()),
                                wasm_encoder::Instruction::RefAsNonNull,
                            ],
                        },
                        table::ProductKind::Composite => unimplemented!(
                            "Composite user-defined types not supported in clause guards"
                        ),
                    }
                }
                Some(Binding::Constant(..)) => unreachable!("Constants shouldn't appear here"),
                Some(Binding::Function(..)) => {
                    unreachable!("Gleam does not support function references in clause guards")
                }
                None => unreachable!("Name does not exist in environment"),
            }
        }
        ClauseGuard::Constant(constant) => emit_constant(constant, env, table),
        ClauseGuard::TupleIndex { .. } => todo!("Tuples not implemented yet"),
        ClauseGuard::FieldAccess { .. } => todo!("Field access not implemented yet"),
        ClauseGuard::ModuleSelect { .. } => todo!("Modules not implemented yet"),
    }
}

fn emit_binary_operation(
    env: &Environment<'_>,
    locals: &mut LocalStore,
    strings: &mut Strings,
    table: &SymbolTable,
    // only used to disambiguate equals
    _typ: &Type,
    name: BinOp,
    left: &TypedExpr,
    right: &TypedExpr,
) -> WasmInstructions {
    match name {
        BinOp::AddInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::add().lst);
            insts
        }
        BinOp::SubInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::sub().lst);
            insts
        }
        BinOp::MultInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::mul().lst);
            insts
        }
        BinOp::DivInt => {
            /*
               left
               right
               0
               ==
               if
                   right
                   div
               else
                   drop
                   right
               end
            */
            // we need to evaluate the right operand only once
            // create a local
            let right_id = locals.new_id();
            locals.insert(
                right_id,
                Local {
                    id: right_id,
                    name: "@fdiv_rhs_temp".into(),
                    wasm_type: WasmTypeImpl::Int,
                },
            );

            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);

            insts.lst.extend(right_insts.lst);
            insts
                .lst
                .push(wasm_encoder::Instruction::LocalTee(right_id.id()));
            insts.lst.extend(integer::const_(0).lst);
            insts.lst.extend(integer::eq().lst);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::FunctionType(table.int_division.unwrap().id()),
            ));

            insts
                .lst
                .push(wasm_encoder::Instruction::LocalGet(right_id.id()));
            insts.lst.extend(integer::div().lst);

            insts.lst.push(wasm_encoder::Instruction::Else);

            insts.lst.push(wasm_encoder::Instruction::Drop);
            insts
                .lst
                .push(wasm_encoder::Instruction::LocalGet(right_id.id())); // 0

            insts.lst.push(wasm_encoder::Instruction::End);

            insts
        }
        BinOp::RemainderInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::rem().lst);
            insts
        }
        BinOp::And => {
            // short circuiting behavior: if left is false, don't evaluate right
            let mut insts = emit_expression(left, env, locals, strings, table);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::Result(WasmTypeImpl::Bool.to_val_type()),
            ));

            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);

            insts.lst.push(wasm_encoder::Instruction::Else);
            insts.lst.push(wasm_encoder::Instruction::I32Const(0));
            insts.lst.push(wasm_encoder::Instruction::End);
            insts
        }
        BinOp::Or => {
            // short circuiting behavior: if left is true, don't evaluate right
            let mut insts = emit_expression(left, env, locals, strings, table);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::Result(WasmTypeImpl::Bool.to_val_type()),
            ));
            insts.lst.push(wasm_encoder::Instruction::I32Const(1));
            insts.lst.push(wasm_encoder::Instruction::Else);

            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);

            insts.lst.push(wasm_encoder::Instruction::End);
            insts
        }
        BinOp::Eq => {
            // check types
            assert_eq!(left.type_(), right.type_(), "Expected equal types");

            let type_ = left.type_();
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(
                emit_equality_test(&FieldType::from_gleam_type(type_, env, table), table).lst,
            );
            insts
        }
        BinOp::NotEq => {
            // check types
            assert_eq!(left.type_(), right.type_(), "Expected equal types");

            let type_ = left.type_();
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32Eqz);
            insts.lst.extend(
                emit_equality_test(&FieldType::from_gleam_type(type_, env, table), table).lst,
            );
            insts
        }
        BinOp::LtInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::lt().lst);
            insts
        }
        BinOp::LtEqInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::lte().lst);
            insts
        }
        BinOp::LtFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Lt);
            insts
        }
        BinOp::LtEqFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Le);
            insts
        }
        BinOp::GtEqInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::gte().lst);
            insts
        }
        BinOp::GtInt => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.extend(integer::gt().lst);
            insts
        }
        BinOp::GtEqFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Ge);
            insts
        }
        BinOp::GtFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Gt);
            insts
        }
        BinOp::AddFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Add);
            insts
        }
        BinOp::SubFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Sub);
            insts
        }
        BinOp::MultFloat => {
            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::F64Mul);
            insts
        }
        BinOp::DivFloat => {
            /*
               left
               right
               0.0
               ==
               if
                   right
                   div
               else
                   drop
                   right
               end
            */
            // we need to evaluate the right operand only once
            // create a local
            let right_id = locals.new_id();
            locals.insert(
                right_id,
                Local {
                    id: right_id,
                    name: "@fdiv_rhs_temp".into(),
                    wasm_type: WasmTypeImpl::Float,
                },
            );

            let mut insts = emit_expression(left, env, locals, strings, table);
            let right_insts = emit_expression(right, env, locals, strings, table);

            insts.lst.extend(right_insts.lst);
            insts
                .lst
                .push(wasm_encoder::Instruction::LocalTee(right_id.id()));
            insts.lst.push(wasm_encoder::Instruction::F64Const(0.0));
            insts.lst.push(wasm_encoder::Instruction::F64Eq);

            insts.lst.push(wasm_encoder::Instruction::If(
                wasm_encoder::BlockType::FunctionType(table.float_division.unwrap().id()),
            ));

            insts
                .lst
                .push(wasm_encoder::Instruction::LocalGet(right_id.id()));
            insts.lst.push(wasm_encoder::Instruction::F64Div);

            insts.lst.push(wasm_encoder::Instruction::Else);

            insts.lst.push(wasm_encoder::Instruction::Drop);
            insts
                .lst
                .push(wasm_encoder::Instruction::LocalGet(right_id.id())); // 0.0

            insts.lst.push(wasm_encoder::Instruction::End);

            insts
        }
        BinOp::Concatenate => todo!("<> not implemented yet"),
    }
}

fn parse_float(value: &str) -> f64 {
    let val = value.replace("_", "");
    val.parse()
        .expect("expected float to be a valid decimal float")
}
