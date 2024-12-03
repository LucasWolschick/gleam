pub fn int_to_string(n: Int) -> String {
  case n {
    _ if n < 0 -> "-" <> int_to_string(-n)
    0 -> "0"
    1 -> "1"
    2 -> "2"
    3 -> "3"
    4 -> "4"
    5 -> "5"
    6 -> "6"
    7 -> "7"
    8 -> "8"
    9 -> "9"
    _ -> int_to_string(n / 10) <> int_to_string(n % 10)
  }
}
