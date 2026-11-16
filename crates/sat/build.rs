//! Compiles the vendored CaDiCaL (`vendor/cadical`) and the shim that
//! collects its proof (`src/shim.cpp`) into one static library.
use std::path::Path;

fn main() {
    let src = Path::new("../../vendor/cadical/src");
    let mut cpp = cc::Build::new();
    cpp.cpp(true)
        .std("c++11")
        .opt_level(3)
        .define("NDEBUG", None)
        .define("NBUILD", None)
        .include(src)
        .warnings(false)
        .file("src/shim.cpp");
    let mut c = cc::Build::new();
    c.opt_level(3).define("NDEBUG", None).define("NBUILD", None).include(src).warnings(false);
    let mut entries: Vec<_> = std::fs::read_dir(src).expect("vendor/cadical/src").map(|e| e.expect("entry").path()).collect();
    entries.sort();
    for path in entries {
        match path.extension().and_then(|e| e.to_str()) {
            Some("cpp") => {
                cpp.file(&path);
            }
            Some("c") => {
                c.file(&path);
            }
            _ => {}
        }
        println!("cargo:rerun-if-changed={}", path.display());
    }
    println!("cargo:rerun-if-changed=src/shim.cpp");
    c.compile("cadical_c");
    cpp.compile("cadical");
}
