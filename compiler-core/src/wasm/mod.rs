mod encoder;
mod index_generator;
mod scope;

use std::{collections::HashMap, sync::Arc};

use index_generator::IndexGenerator;
use itertools::Itertools;
use scope::Scope;

use crate::{
    ast::{
        BinOp, CustomType, Function, Pattern, Statement, TypedArg, TypedAssignment, TypedExpr,
        TypedFunction, TypedModule, TypedStatement,
    },
    io::FileSystemWriter,
    type_::Type,
};

enum WasmType {
    FunctionType {
        parameters: Vec<WasmPrimitive>,
        returns: WasmPrimitive,
    },
}

impl WasmType {
    fn from_function(f: &TypedFunction) -> Self {
        let mut parameters = vec![];

        for arg in &f.arguments {
            if arg.type_.is_int() {
                parameters.push(WasmPrimitive::Int);
            } else {
                todo!("Only int parameters")
            }
        }

        let returns = if f.return_type.is_int() {
            WasmPrimitive::Int
        } else {
            todo!("Only int return types")
        };

        WasmType::FunctionType {
            parameters,
            returns,
        }
    }
}

type LocalIndexGenerator = IndexGenerator<Arc<Type>>;
type TypeIndexGenerator = IndexGenerator<WasmType>;
type FunctionIndexGenerator = IndexGenerator<()>;

type FunctionIndex = u32;
type TypeIndex = u32;
type FunctionTypeMap = HashMap<FunctionIndex, TypeIndex>;

pub fn module(writer: &impl FileSystemWriter, ast: &TypedModule) {
    dbg!(&ast);
    let module = construct_module(ast);
    let bytes = encoder::emit(module);
    writer.write_bytes("out.wasm".into(), &bytes[..]).unwrap();
}

struct WasmModule {
    functions: Vec<WasmFunction>,
    types: Vec<WasmType>,
}

fn construct_module(ast: &TypedModule) -> WasmModule {
    use crate::ast::TypedDefinition;

    // FIRST PASS: generate indices for all functions and types in the top-level module
    let mut function_index_generator = FunctionIndexGenerator::new();
    let mut type_index_generator = TypeIndexGenerator::new();
    let mut function_type_map = HashMap::new();
    let mut root_environment = Scope::new();

    // TODO: handle custom types
    // TODO: handle local function/type definitions
    for definition in &ast.definitions {
        match definition {
            TypedDefinition::Function(f) => {
                let function_index = function_index_generator.new_index(());
                root_environment = root_environment.set(&f.name, function_index);
                let function_type_index =
                    type_index_generator.new_index(WasmType::from_function(f));
                let _ = function_type_map.insert(function_index, function_type_index);
            }
            _ => {}
        }
    }

    // SECOND PASS: generate the actual function bodies
    let mut functions = vec![];
    for definition in &ast.definitions {
        match definition {
            TypedDefinition::Function(f) => {
                let function_index = root_environment.get(&f.name).unwrap();
                let function_type_index = *function_type_map.get(&function_index).unwrap();
                let function = emit_function(
                    f,
                    &type_index_generator,
                    function_type_index,
                    function_index,
                    Arc::clone(&root_environment),
                );
                functions.push(function);
            }
            _ => todo!("unimplemented"),
        }
    }

    WasmModule {
        functions,
        types: type_index_generator.items,
    }
}

#[derive(Copy, Clone, Debug)]
enum WasmPrimitive {
    Int,
}

impl WasmPrimitive {
    fn to_val_type(self) -> wasm_encoder::ValType {
        match self {
            WasmPrimitive::Int => wasm_encoder::ValType::I32,
        }
    }
}

struct WasmInstructions {
    lst: Vec<wasm_encoder::Instruction<'static>>,
}

struct WasmFunction {
    type_index: TypeIndex,
    instructions: WasmInstructions,
    locals: Vec<WasmPrimitive>,
    function_index: FunctionIndex,
}

fn emit_function(
    function: &TypedFunction,
    type_map: &TypeIndexGenerator,
    type_index: u32,
    function_index: u32,
    top_level_env: Arc<Scope>,
) -> WasmFunction {
    let mut env = Scope::new_enclosing(top_level_env);
    let mut locals = LocalIndexGenerator::new();
    let function_type = type_map.get(type_index).unwrap();
    let n_params = match function_type {
        WasmType::FunctionType { parameters, .. } => parameters.len(),
        _ => unreachable!(),
    };

    for arg in &function.arguments {
        // get a variable number
        let idx = locals.new_index(Arc::clone(&arg.type_));
        // add arguments to the environment
        env = env.set(
            &arg.names
                .get_variable_name()
                .cloned()
                .unwrap_or_else(|| format!("#{idx}").into()),
            idx,
        );
    }

    let (_, locals, mut instructions) = emit_statement_list(env, locals, &function.body);
    instructions.lst.push(wasm_encoder::Instruction::End);

    WasmFunction {
        function_index,
        type_index,
        instructions,
        locals: locals
            .items
            .into_iter()
            .skip(n_params)
            .map(|x| {
                if x.is_int() {
                    WasmPrimitive::Int
                } else {
                    todo!("Only int return types")
                }
            })
            .collect_vec(),
    }
}

fn emit_statement_list(
    env: Arc<Scope>,
    locals: LocalIndexGenerator,
    statements: &[TypedStatement],
) -> (Arc<Scope>, LocalIndexGenerator, WasmInstructions) {
    let mut instructions = WasmInstructions { lst: vec![] };
    let mut env = env;
    let mut locals = locals;

    for statement in statements.into_iter().dropping_back(1) {
        let (new_env, new_locals, new_insts) = emit_statement(statement, env, locals);
        env = new_env;
        locals = new_locals;
        instructions.lst.extend(new_insts.lst);
        instructions.lst.push(wasm_encoder::Instruction::Drop);
    }
    if let Some(statement) = statements.last() {
        let (new_env, new_locals, new_insts) = emit_statement(statement, env, locals);
        env = new_env;
        locals = new_locals;
        instructions.lst.extend(new_insts.lst);
    }

    (env, locals, instructions)
}

fn emit_statement(
    statement: &TypedStatement,
    env: Arc<Scope>,
    locals: LocalIndexGenerator,
) -> (Arc<Scope>, LocalIndexGenerator, WasmInstructions) {
    match statement {
        Statement::Expression(expression) => emit_expression(expression, env, locals),
        Statement::Assignment(assignment) => emit_assignment(assignment, env, locals),
        _ => todo!("Only expressions and assignments"),
    }
}

fn emit_assignment(
    assignment: &TypedAssignment,
    env: Arc<Scope>,
    locals: LocalIndexGenerator,
) -> (Arc<Scope>, LocalIndexGenerator, WasmInstructions) {
    // only non-assertions
    if assignment.kind.is_assert() {
        todo!("Only non-assertions");
    }

    // only support simple assignments for now
    match assignment.pattern {
        Pattern::Variable {
            ref name,
            ref type_,
            ..
        } => {
            // emit value
            let (env, mut locals, mut insts) = emit_expression(&assignment.value, env, locals);
            // add variable to the environment
            let id = locals.new_index(Arc::clone(type_));
            let env = env.set(&name, id);
            // create local
            insts
                .lst
                .push(wasm_encoder::Instruction::LocalTee(env.get(name).unwrap()));

            (env, locals, insts)
        }
        _ => todo!("Only simple assignments"),
    }
}

fn emit_expression(
    expression: &TypedExpr,
    env: Arc<Scope>,
    locals: LocalIndexGenerator,
) -> (Arc<Scope>, LocalIndexGenerator, WasmInstructions) {
    match expression {
        TypedExpr::Int { value, .. } => {
            let val = parse_integer(value);
            (
                env,
                locals,
                WasmInstructions {
                    lst: vec![wasm_encoder::Instruction::I32Const(val)],
                },
            )
        }
        TypedExpr::NegateInt { value, .. } => {
            let (env, locals, mut insts) = emit_expression(value, env, locals);
            insts.lst.push(wasm_encoder::Instruction::I32Const(-1));
            insts.lst.push(wasm_encoder::Instruction::I32Mul);
            (env, locals, insts)
        }
        TypedExpr::Block { statements, .. } => {
            // create new scope
            // TODO: fix environment pop
            // maybe use a block instruction?
            let (_, locals, statements) = emit_statement_list(Scope::new_enclosing(Arc::clone(&env)), locals, statements);
            (env, locals, statements)
        },
        TypedExpr::BinOp {
            typ,
            name,
            left,
            right,
            ..
        } => emit_binary_operation(env, locals, typ, *name, left, right),
        TypedExpr::Var {
            constructor, name, ..
        } => {
            if !constructor.is_local_variable() {
                todo!("Only local variables");
            }

            dbg!(&env);
            let index = env.get(name).unwrap();
            (
                env,
                locals,
                WasmInstructions {
                    lst: vec![wasm_encoder::Instruction::LocalGet(index)],
                },
            )
        },
        _ => todo!("Only integer constants, integer negation, blocks, binary operations, case and variable accesses"),
    }
}

fn emit_binary_operation(
    env: Arc<Scope>,
    locals: LocalIndexGenerator,
    // only used to disambiguate equals
    _typ: &Type,
    name: BinOp,
    left: &TypedExpr,
    right: &TypedExpr,
) -> (Arc<Scope>, LocalIndexGenerator, WasmInstructions) {
    match name {
        BinOp::AddInt => {
            let (env, locals, mut insts) = emit_expression(left, env, locals);
            let (env, locals, right_insts) = emit_expression(right, env, locals);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32Add);
            (env, locals, insts)
        }
        BinOp::SubInt => {
            let (env, locals, mut insts) = emit_expression(left, env, locals);
            let (env, locals, right_insts) = emit_expression(right, env, locals);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32Sub);
            (env, locals, insts)
        }
        BinOp::MultInt => {
            let (env, locals, mut insts) = emit_expression(left, env, locals);
            let (env, locals, right_insts) = emit_expression(right, env, locals);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32Mul);
            (env, locals, insts)
        }
        BinOp::DivInt => {
            let (env, locals, mut insts) = emit_expression(left, env, locals);
            let (env, locals, right_insts) = emit_expression(right, env, locals);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32DivS);
            (env, locals, insts)
        }
        BinOp::RemainderInt => {
            let (env, locals, mut insts) = emit_expression(left, env, locals);
            let (env, locals, right_insts) = emit_expression(right, env, locals);
            insts.lst.extend(right_insts.lst);
            insts.lst.push(wasm_encoder::Instruction::I32RemS);
            (env, locals, insts)
        }
        _ => todo!("Only integer arithmetic"),
    }
}

fn parse_integer(value: &str) -> i32 {
    let val = value.replace("_", "");

    // TODO: support integers other than i32
    // why do i have do this at codegen?
    let int = if val.starts_with("0b") {
        // base 2 literal
        i32::from_str_radix(&val[2..], 2).expect("expected int to be a valid binary integer")
    } else if val.starts_with("0o") {
        // base 8 literal
        i32::from_str_radix(&val[2..], 8).expect("expected int to be a valid octal integer")
    } else if val.starts_with("0x") {
        // base 16 literal
        i32::from_str_radix(&val[2..], 16).expect("expected int to be a valid hexadecimal integer")
    } else {
        // base 10 literal
        i32::from_str_radix(&val, 10).expect("expected int to be a valid decimal integer")
    };

    int
}
