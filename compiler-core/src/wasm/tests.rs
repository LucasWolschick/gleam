#[test]
fn string_unescape() {
    assert_eq!(
        crate::wasm::string::unescape(r#"sure \\ \n \"its\" \t works! \u{263A}, \r or \f not..."#),
        "sure \\ \n \"its\" \t works! ☺, \r or \x0C not..."
    );
}

#[test]
fn int_parse() {
    use crate::wasm::integer;
    assert_eq!(integer::parse("0b1_0_1"), 5);
    assert_eq!(integer::parse("0o7_654_321_0"), 16434824);
    assert_eq!(integer::parse("0xAbc_DEF_1"), 180150001);
    assert_eq!(integer::parse("759_012"), 759_012);
}

#[test]
fn bool() {
    test_file("bool.gleam");
}

#[test]
fn int() {
    test_file("int.gleam");
}

#[test]
fn float() {
    test_file("float.gleam");
}

#[test]
fn string() {
    test_file("string.gleam");
}

#[test]
fn prelude() {
    test_file("prelude.gleam");
}

#[cfg(test)]
fn test_file(file: &str) {
    let mut case = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    case.extend(["src", "wasm", "tests", file].iter());
    let code = std::fs::read_to_string(case).unwrap();
    let _ = build_and_run(&code).success();
}

#[cfg(test)]
fn build_and_run(code: &str) -> assert_cmd::assert::Assert {
    use crate::io::FileSystemReader;
    use assert_cmd::prelude::OutputAssertExt;

    let module = crate::wasm::build_module(code);
    let mut fs = crate::io::memory::InMemoryFileSystem::new();
    crate::wasm::module(&mut fs, &module);

    let dir = tempdir::TempDir::new("gleam").unwrap();
    let out = dir.path().join("out.wasm");
    std::fs::write(&out, fs.read_bytes("out.wasm".into()).unwrap()).unwrap();

    std::process::Command::new("wasmtime")
        .args(["-W", "all-proposals=y", &out.to_str().unwrap()])
        .assert()
}
