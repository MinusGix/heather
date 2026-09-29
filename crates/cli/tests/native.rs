//! Exercise the actual exported bytes through the host assembler and linker.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn source_to_native_binary() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/native-integration-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let assembly = output.join("mix.s");
    let tsv = output.join("timings.tsv");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["compile-x86", "examples/x86-native/mix.hthr", "mix", "-o"])
        .arg(&assembly).args(["--cache-dir", "target/native-test-images"])
        .arg("--item-timings").arg(&tsv)
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    item_timings_cover_the_certificate(&tsv, &output.join("mix.certificate.hthr"));
    assert!(!output.join("mix.certificate.unchecked.hthr").exists(), "a published certificate has no unchecked copy");
    assert!(!output.join("timings.open.tsv").exists(), "and a finished build no open scopes");
    let binary = output.join("mix");
    let linked = Command::new("cc").current_dir(&root)
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "examples/x86-native/main.c"])
        .arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let native = Command::new(&binary).output().unwrap();
    assert!(native.status.success(), "{}", String::from_utf8_lossy(&native.stdout));
    assert!(String::from_utf8_lossy(&native.stdout).contains("10005 native cases passed"));
    std::fs::remove_dir_all(output).unwrap();
}

/// `--item-timings` is attribution, so its table must account for every
/// declaration of the certificate it was asked about — a table that silently
/// omits the expensive ones would mislead exactly where it is consulted.
///
/// The certificate goes through the semantic session, so a run at an
/// unchanged compiler replays its image from `target/native-test-images`:
/// then nothing was elaborated and the module row, carrying the replay's
/// decode and recheck, is the whole account. The per-declaration check runs
/// whenever the certificate was elaborated — every first run after a change
/// to the compiler or the generator.
fn item_timings_cover_the_certificate(tsv: &std::path::Path, certificate: &std::path::Path) {
    let table = std::fs::read_to_string(tsv).unwrap();
    let mut lines = table.lines();
    let header: Vec<&str> = lines.next().unwrap().split('\t').collect();
    assert_eq!(&header[..5], ["scope", "module", "item", "total_ns", "other_ns"]);
    assert!(header.contains(&"kernel_gate_ns"), "the gate keeps a column of its own");
    assert!(header.contains(&"conv_misses"), "the kernel's counters are columns too");
    let column = |name: &str| header.iter().position(|h| *h == name).unwrap();
    let (decode, recheck) = (column("image_decode_ns"), column("image_recheck_ns"));
    let mut rows = std::collections::HashSet::new();
    let mut replayed = None;
    for line in lines {
        let cells: Vec<&str> = line.split('\t').collect();
        assert_eq!(cells.len(), header.len(), "row {line:?}");
        cells[3].parse::<u64>().unwrap();
        if cells[0] == "item" && cells[1] == "mix_native_certificate" {
            rows.insert(cells[2].to_string());
        }
        if cells[0] == "module" && cells[1] == "mix_native_certificate" {
            replayed = Some(cells[decode] != "0" && cells[recheck] != "0");
        }
    }
    let replayed = replayed.expect("the certificate has a module row");
    if rows.is_empty() {
        assert!(replayed, "an elaborated certificate has item rows; this one has none and no replay either");
        return;
    }
    let source = std::fs::read_to_string(certificate).unwrap();
    let mut declarations = 0;
    for line in source.lines() {
        let Some(rest) = line.strip_prefix("theorem ").or_else(|| line.strip_prefix("fn ")) else { continue };
        let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        assert!(rows.contains(&name), "no timing row for `{name}`");
        declarations += 1;
    }
    assert!(declarations > 1, "the certificate declares more than one item");
    let mut imports = std::collections::HashSet::new();
    for line in source.lines() {
        let Some(module) = line.strip_prefix("import ").and_then(|rest| rest.strip_suffix(';')) else { continue };
        assert!(rows.contains(&format!("import {module}")), "no timing row for `import {module}`");
        imports.insert(module);
    }
    assert!(rows.len() >= declarations + imports.len(), "{} rows for {declarations} declarations", rows.len());
    assert!(rows.iter().any(|name| name == "mix_native_exported_bytes"));
}

#[test]
fn source_to_standalone_elf_without_a_toolchain() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/elf-integration-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let binary = output.join("mix");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        // No child compiler/assembler/linker can be found through PATH.
        .env("PATH", &output)
        .args(["build-x86", "examples/x86-native/mix.hthr", "mix", "--arg", "0x14", "--arg", "0b10110", "-o"])
        .arg(&binary).args(["--cache-dir", "target/native-test-images"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let bytes = std::fs::read(&binary).unwrap();
    assert_eq!(&bytes[..4], b"\x7fELF");
    assert_eq!(u64::from_le_bytes(bytes[24..32].try_into().unwrap()), 0x4000b0);
    assert_eq!(u32::from_le_bytes(bytes[68..72].try_into().unwrap()), 5); // RX
    assert_eq!(u32::from_le_bytes(bytes[124..128].try_into().unwrap()), 6); // RW stack
    // The request carries the full result, while Linux reports its low byte:
    // mix(0x14, 0b10110) = 0x0123456789ABCE33, and 0x33 = 51.
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(51));
    let certificate = std::fs::read_to_string(output.join("mix.certificate.hthr")).unwrap();
    for claim in ["_entry_graph", "_inline_trace", "_exit_request", "_elf_file_correct", "_elf_entry_code", "_loaded_image", "_loaded_fetches", "_loaded_trace"] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    // An invalid argument must fail before publishing either output. (It is
    // refused while the options are read, before the source is opened, so
    // this run costs a process start and no elaboration.)
    let rejected = output.join("bad");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["build-x86", "examples/x86-native/mix.hthr", "mix", "--arg", "-1", "--arg", "0", "-o"])
        .arg(&rejected).output().unwrap();
    assert!(!result.status.success());
    assert!(!rejected.exists());
    assert!(!output.join("bad.certificate.hthr").exists());
    std::fs::remove_dir_all(output).unwrap();
}
