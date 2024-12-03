use wasm_encoder::{Instruction, ValType};

use super::encoder::WasmInstructions;

pub type Representation = i32;

pub const VAL_TYPE: ValType = ValType::I32;

pub fn add() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Add)
}

pub fn sub() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Sub)
}

pub fn mul() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Mul)
}

pub fn div() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32DivS)
}

pub fn rem() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32RemS)
}

pub fn const_(value: Representation) -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Const(value))
}

pub fn eq() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Eq)
}

pub fn ne() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32Ne)
}

pub fn lt() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32LtS)
}

pub fn gt() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32GtS)
}

pub fn lte() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32LeS)
}

pub fn gte() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32GeS)
}

pub fn float_to_int() -> WasmInstructions {
    WasmInstructions::single(Instruction::I32TruncF64S)
}

pub fn const_expr_initializer(arg: Representation) -> wasm_encoder::ConstExpr {
    wasm_encoder::ConstExpr::i32_const(arg)
}

pub fn parse(value: &str) -> Representation {
    let val = value.replace("_", "");

    // TODO: support integers other than i32
    // why do i have do this at codegen?
    if let Some(val) = val.strip_prefix("0b") {
        // base 2 literal
        i32::from_str_radix(val, 2).expect("expected int to be a valid binary integer")
    } else if let Some(val) = val.strip_prefix("0o") {
        // base 8 literal
        i32::from_str_radix(val, 8).expect("expected int to be a valid octal integer")
    } else if let Some(val) = val.strip_prefix("0x") {
        // base 16 literal
        i32::from_str_radix(val, 16).expect("expected int to be a valid hexadecimal integer")
    } else {
        // base 10 literal
        val.parse()
            .expect("expected int to be a valid decimal integer")
    }
}
