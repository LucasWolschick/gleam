@external(wasm, "gleam", "int_to_string")
fn int_to_string(str: Int) -> String

pub fn main() {
  assert_eq(int_to_string(0), "0")
  assert_eq(int_to_string(1234567890), "1234567890")
  assert_eq(int_to_string(-1234567890), "-1234567890")
}

fn assert_eq(a: String, b: String) {
  a == b || panic
}