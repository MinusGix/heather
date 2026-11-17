//! cat, compiled by the effectful source compiler and written as an ELF by
//! `heather write-elf`, run as a Linux process: it copies stdin to stdout and
//! exits 0, and exits 1 when a read or a write fails
//! (`lib/native/native_cat_executable.hthr` is its theorem). Beside it, a
//! program with no proof of its own gets the compiler's theorem in its
//! certificate, and the programs that theorem would not cover are refused
//! with their reason (issues/native-elf-every-program.md).
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use heather_cli::showcase;

/// One `write-elf` of cat through the library gate's image store, whose
/// closure replays what the gate built (every module is keyed by its own
/// closure, `docs/infrastructure/module-dag-design.md`); the suite runs the gate first and
/// starts this target once the images it replays are built
/// (`PREREQUISITES` in scripts/run-test-targets.mjs). In the suite's stale lanes it replays images an earlier
/// build wrote, as the gate does: without that, every compiler edit made
/// this test rebuild the whole closure from source.
fn write_cat(output: &Path) {
    let result = write_elf("lib/native/native_cat_executable.hthr", "cat_source", output);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
}

fn write_elf(file: &str, source: &str, output: &Path) -> std::process::Output {
    write_elf_with(file, source, output, &[])
}

fn write_elf_with(file: &str, source: &str, output: &Path, options: &[&str]) -> std::process::Output {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["write-elf", file, source, "-o"])
        .arg(output)
        .args(options)
        .arg("--cache-dir").arg(showcase::cli_check_images());
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    cmd.output().unwrap()
}

/// A directory of its own under `target/`, for one test's files.
fn scratch(name: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = showcase::repo_root().join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn run(binary: &Path, input: &[u8], stdout: Stdio) -> (Option<i32>, Vec<u8>) {
    let mut child = Command::new(binary).stdin(Stdio::piped()).stdout(stdout).stderr(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    // A writer of its own, so a large input cannot deadlock against a full
    // stdout pipe.
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    assert!(out.stderr.is_empty(), "the program wrote to stderr");
    (out.status.code(), out.stdout)
}

#[test]
fn compiled_cat_runs_as_cat() {
    let dir = scratch("cat");
    let binary = dir.join("cat");
    write_cat(&binary);
    let certificate = std::fs::read_to_string(dir.join("cat.certificate.hthr")).expect("the certificate is published beside the file");
    // cat is long enough that its emission is stated a part at a time, and
    // joined by each of the three (crates/cli/src/native/emission.rs): a
    // sequence's by `emits_then_checked` where the allocation's check gives
    // the set live between its parts, otherwise by `emits_then_of`.
    for join in ["Stmt::emits_then_", "Stmt::emits_repeat_of", "Stmt::emits_branch_of"] {
        assert!(certificate.contains(join), "the certificate joins parts by `{join}`");
    }
    assert!(!dir.join("cat.certificate.unchecked.hthr").exists(), "and no unchecked copy is left");
    let file = std::fs::read(&binary).unwrap();
    assert_eq!(&file[..4], b"\x7fELF");

    // Nothing, a line, and more than one buffer's worth of every byte value.
    let every: Vec<u8> = (0..5000u32).map(|i| (i * 7 % 256) as u8).collect();
    for input in [&b""[..], b"hello, cat\n", &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "cat exits 0 at the end of its input");
        assert_eq!(out, input, "and has sent what it read");
    }

    // A write that fails: stdout is full.
    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&binary, b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
    }

    // A read that fails: stdin is a directory.
    let status = Command::new(&binary).stdin(std::fs::File::open(&dir).unwrap()).stdout(Stdio::null()).status().unwrap();
    assert_eq!(status.code(), Some(1), "a failed read exits 1");

    std::fs::remove_dir_all(dir).unwrap();
}

/// A program eight times cat's code over (`cat_x8`, in the probes below)
/// builds, its layout and bytes checked by a table of its labels, and runs
/// as cat: write-elf's build grows with the code, not with its square
/// (issues/native-compile-linear-layout.md).
#[test]
fn larger_program_runs_as_cat() {
    let dir = scratch("cat_x8");
    let binary = dir.join("cat_x8");
    let result = write_elf(PROBES, "cat_x8", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let certificate = std::fs::read_to_string(dir.join("cat_x8.certificate.hthr")).unwrap();
    for by in ["laid_out_of", "piece_by"] {
        assert!(certificate.contains(by), "the certificate's layout and bytes go by the table (`{by}`)");
    }
    let every: Vec<u8> = (0..20000u32).map(|i| (i * 13 % 256) as u8).collect();
    for input in [&b""[..], b"hello, cat\n", &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "it exits 0 at the end of its input");
        assert_eq!(out, input, "and has sent what it read");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// A program with a MiB buffer (`mib_cat`: cat reading up to a MiB at a
/// time) builds, runs as cat, and carries the compiler's theorem: its data
/// segment is its layout in whole pages, zero-filled, so it takes nothing in
/// the file (issues/native-data-capacity.md).
#[test]
fn mebibyte_buffer_runs_as_cat() {
    let dir = scratch("mib_cat");
    let binary = dir.join("mib_cat");
    let result = write_elf(PROBES, "mib_cat", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    // Words, the buffer, a scratch range one byte longer and the saved RSP,
    // 2097321 bytes, in 513 pages.
    let size = 513 * 4096u64;
    let certificate = std::fs::read_to_string(dir.join("mib_cat.certificate.hthr")).unwrap();
    for statement in [&format!("fn mib_cat_elf_size() → Nat {{ {size} }}")[..], "theorem mib_cat_elf_fits()", "theorem mib_cat_elf_runs("] {
        assert!(certificate.contains(statement), "the certificate states `{statement}`");
    }
    let file = std::fs::read(&binary).unwrap();
    assert!(file.len() < 4096, "the segment takes nothing in the file, which is {} bytes", file.len());
    // The RW segment's program header, the third, and its `p_memsz`.
    let memsz = u64::from_le_bytes(file[64 + 2 * 56 + 40..][..8].try_into().unwrap());
    assert_eq!(memsz, size, "the segment is the program's size");

    // More than two buffers' worth, through a pipe and from a file, whose
    // reads fill the buffer whole.
    let every: Vec<u8> = (0..3_000_000u32).map(|i| (i * 7 % 251) as u8).collect();
    for input in [&b""[..], b"hello, cat\n", &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "it exits 0 at the end of its input");
        assert_eq!(out, input, "and has sent what it read");
    }
    let path = dir.join("input");
    std::fs::write(&path, &every).unwrap();
    let out = Command::new(&binary).stdin(std::fs::File::open(&path).unwrap()).output().unwrap();
    assert_eq!(out.status.code(), Some(0), "it exits 0 at the end of the file");
    assert!(out.stdout == every, "and has sent the file, a MiB a read");
    std::fs::remove_dir_all(dir).unwrap();
}

/// The probes `lib/_tests/native/native_compile_tests.hthr` holds, which
/// import none of the certificate's modules.
const PROBES: &str = "lib/_tests/native/native_compile_tests.hthr";
const STRUCTURED: &str = "lib/_tests/native/native_structured_tests.hthr";
const BUILT: &str = "lib/_tests/native/native_build_tests.hthr";

/// A program that is not cat gets the compiler's theorem with no proof of
/// its own: `head -c 10` copies ten bytes of any longer input and exits 0.
#[test]
fn every_written_program_gets_its_theorem() {
    let dir = scratch("head10");
    let binary = dir.join("head10");
    let result = write_elf(PROBES, "head10", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let certificate = std::fs::read_to_string(dir.join("head10.certificate.hthr")).unwrap();
    // Its theorem is over its contract, whose lines the certificate names
    // and the compile prints. On the system's stack the room below RSP is
    // one of them, and checked: the entry code stores into each page of it,
    // and the theorem's conclusion is the claim over every memory Linux may
    // leave at those stores (`Contract::Runs`). Where the stack is, a page
    // and the room above the segment, is what stays taken on trust.
    for statement in ["theorem head10_elf_fits()", "theorem head10_elf_runs(", "start: head10_elf_contract().Start(head10_elf_file(), top, args)(s)",
        "head10_elf_contract().Runs(top, head10().denote(args))(s)", "fn head10_elf_from() → StackFrom { FromSystem }",
        "fn head10_elf_stack() → List<BitVec(8)> {",
        "theorem head10_elf_presumes(): head10_elf_contract().lines() = [Processor, FileLoaded(4096), EntryAddress, CommandLine, StackAbove(4280), StackRoom(184), StackGrowth, CallsAnswered, NoFatalSignal]"] {
        assert!(certificate.contains(statement), "the certificate states `{statement}`");
    }
    let printed = String::from_utf8_lossy(&result.stdout).to_string();
    for line in ["`head10` presumes of the system that runs it:", "  [standard]  execution starts at the header's entry address (ELF gABI)",
        "  [presumed]  the stack pointer as the process starts is 4280 bytes or more above the data segment's end, in the lower half of the address space",
        "  [checked]   184 bytes below the stack pointer as the process starts are usable: the program stores into each page of them as it starts, and ends there with a signal if one is refused",
        "  [standard]  a store within a page below the stack extends the stack or ends the process with a signal (Linux: mmap(2), getrlimit(2))",
        "  [presumed]  no fatal signal is delivered, the kernel's out-of-memory kill included"] {
        assert!(printed.contains(line), "the compile prints `{line}`:\n{printed}");
    }
    // The file carries the same lines as an ELF note after its code, and the
    // certificate states that note is the contract's.
    assert!(certificate.contains("theorem head10_elf_note_is(): head10_elf_contract().note() = head10_elf_note()"), "the certificate states the note");
    let file = std::fs::read(&binary).unwrap();
    let text = String::from_utf8_lossy(&file).to_string();
    for line in ["Heather contract 1: what this program presumes of the system that runs it.\nA claim by its compiler, unverified unless checked against the file's certificate.\n",
        "[checked]   184 bytes below the stack pointer as the process starts are usable",
        "[presumed]  no fatal signal is delivered, the kernel's out-of-memory kill included\n"] {
        assert!(text.contains(line), "the file carries `{line}`");
    }
    // The file starts by keeping RSP, and stores a byte 184 below it before
    // anything else: `mov rdi, rsp`, then the touch `mov [rbx], al`, then
    // `mov rsp, rdi`.
    let entry = usize::try_from(u64::from_le_bytes(file[24..32].try_into().unwrap()) - 0x400000).unwrap();
    assert_eq!(&file[entry..][..3], [0x48, 0x89, 0xe7], "the entry code keeps RSP in RDI");
    assert_eq!(&file[entry + 19 + 13..][..6], [0x40, 0x88, 0x03, 0x48, 0x89, 0xfc], "one touch, then RSP is put back");
    // The fourth program header is a PT_NOTE.
    assert_eq!(u16::from_le_bytes(file[56..58].try_into().unwrap()), 4, "four program headers");
    assert_eq!(u32::from_le_bytes(file[64 + 3 * 56..][..4].try_into().unwrap()), 4, "the fourth a PT_NOTE");
    let every: Vec<u8> = (0..700u32).map(|i| (i * 7 % 256) as u8).collect();
    for input in [&b"hello, head\n"[..], &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "head -c 10 exits 0");
        assert_eq!(out, &input[..10], "and has sent the first ten bytes");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// Leaves S4 does not take whole compile a node at a time and run: forty
/// nodes summing twenty constants into one word, read and written over its
/// own slot; and a leaf that mixes byte loads and stores with arithmetic
/// (issues/native-compile-wider-leaves.md).
#[test]
fn wider_leaves_run() {
    let dir = scratch("wider");
    let long = dir.join("long_leaf");
    let result = write_elf(PROBES, "long_leaf", &long);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&long, b"", Stdio::piped());
    assert_eq!((code, out.len()), (Some(210), 0), "the forty-node leaf sums 1 to 20");
    let mixed = dir.join("mixed_bytes");
    let result = write_elf(PROBES, "mixed_bytes", &mixed);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&mixed, b"abcdef", Stdio::piped());
    assert_eq!(out, b"Abcdef", "the first byte stored back, less 32");
    assert_eq!(code, Some((97 + 98 + 99 + 100) % 256), "it exits with the first four bytes' sum");
    std::fs::remove_dir_all(dir).unwrap();
}

/// Procedures compile and run (docs/native/native-procedures-design.md): a
/// non-tail recursive sum called from two sites, its body emitted once;
/// the sum of 0..20 at depth 20, whose innermost call is one too deep and
/// exits 139 (`call_depth_status`); a procedure of three parameters and
/// three results, whose status tells any two out of place; two procedures
/// calling each other, each keeping its parameter across its call, and the
/// same a level short of the depth they nest; and a builder tool (`proc`,
/// native_build) summing 0..n for the n bytes it reads, at most 64 calls
/// deep.
#[test]
fn procedures_run() {
    let dir = scratch("procedures");
    let many = [b'a'; 64];
    for (module, source, input, status, why) in [
        (PROBES, "summing", &b""[..], 9, "the sums of 0..2 and 0..3 add to 9"),
        (PROBES, "summing_shallow", &b""[..], 139, "a call past the depth exits 139"),
        (PROBES, "spreading", &b""[..], 59, "three results come back each to its own word"),
        (PROBES, "alternating", &b""[..], 23, "two procedures calling each other, a(5) with a(n) = b(n - 1) + n and b(n) = 2 a(n - 1) + n"),
        (PROBES, "alternating_shallow", &b""[..], 139, "the same six calls at depth five"),
        (BUILT, "summed_input", &b"hello"[..], 15, "five bytes read sum 0..5"),
        (BUILT, "summed_input", &many[..], 139, "sixty-four bytes read nest sixty-five calls, one past the depth"),
    ] {
        let binary = dir.join(source);
        if !binary.exists() {
            let result = write_elf(module, source, &binary);
            assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
        }
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!((code, out.len()), (Some(status), 0), "`{source}`: {why}");
    }
    let certificate = std::fs::read_to_string(dir.join("summing.certificate.hthr")).unwrap();
    for statement in ["theorem summing_elf_procedures()", "compile_calls_of("] {
        assert!(certificate.contains(statement), "the certificate states `{statement}`");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// A function that calls over views links and runs
/// (docs/native/native-library-exports-design.md §3.1, step V4d): the program's
/// statement calls a function that lends its second buffer whole as its
/// callee's first, and exits with the byte the callee stored through the
/// view and read back. With the view lent to read the program is refused:
/// no rows of marks hold of a store through it.
#[test]
fn a_function_lending_a_view_runs() {
    let dir = scratch("views");
    let binary = dir.join("view_program");
    let result = write_elf(PROBES, "view_program", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&binary, b"", Stdio::piped());
    assert_eq!((code, out.len()), (Some(88), 0), "the byte stored through the view comes back");
    let output = dir.join("view_program_read");
    let result = write_elf(PROBES, "view_program_read", &output);
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(!result.status.success(), "`view_program_read` is refused");
    let reason = "`view_program_read` is refused: the functions it calls do not link";
    assert!(stderr.contains(reason) && stderr.contains("no rows of marks hold of them"), "its refusal says `{reason}`:\n{stderr}");
    assert!(!output.exists(), "and nothing is written for it");
    std::fs::remove_dir_all(dir).unwrap();
}

/// Structured regions compile inside a leaf: `tr a-z A-Z` maps the bytes it
/// read with one loop region, a conditional in its body, and writes them
/// back; regions the compile does not take are refused with their reason
/// (issues/native-compile-wider-leaves.md).
#[test]
fn structured_regions_run() {
    let dir = scratch("structured");
    let tr = dir.join("tr_upper");
    let result = write_elf(STRUCTURED, "tr_upper", &tr);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&tr, b"hello, World! z", Stdio::piped());
    assert_eq!(out, b"HELLO, WORLD! Z", "lower-case letters raised, the rest kept");
    assert_eq!(code, Some(15), "it exits with the loop's index at its end, the count read");
    let (code, out) = run(&tr, b"abcdefghijklmnopqrst", Stdio::piped());
    assert_eq!((code, &out[..]), (Some(16), &b"ABCDEFGHIJKLMNOP"[..]), "one read of at most sixteen bytes");
    for (source, reason) in [
        ("uncounted", "`uncounted` is refused at statement 2, a computation: a loop region the compiler does not take"),
        ("clobbers", "`clobbers` is refused at statement 2, a computation: a loop whose words live after it include one it moves or counts with"),
    ] {
        let output = dir.join(source);
        let result = write_elf(STRUCTURED, source, &output);
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success(), "`{source}` is refused");
        assert!(stderr.contains(reason), "`{source}`'s refusal says `{reason}`:\n{stderr}");
        assert!(!output.exists(), "and nothing is written for it");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// The same program on a stack of its own (`--stack segment`): its theorem
/// asks the system for the file loaded, the entry and the command line above
/// the segment (`SegmentStart`, which its contract's `Start` is) and nothing
/// of the stack Linux made: its contract has no line for stack room, and its
/// conclusion is the simulation itself, with no touches before it. It runs.
#[test]
fn a_program_can_carry_its_own_stack() {
    let dir = scratch("head10_segment");
    let binary = dir.join("head10");
    let result = write_elf_with(PROBES, "head10", &binary, &["--stack", "segment"]);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let certificate = std::fs::read_to_string(dir.join("head10.certificate.hthr")).unwrap();
    for statement in ["theorem head10_elf_runs(", "fn head10_elf_from() → StackFrom { FromSegment }", "fn head10_elf_stack() → List<BitVec(8)> {",
        "theorem head10_elf_presumes(): head10_elf_contract().lines() = [Processor, FileLoaded(4096), EntryAddress, CommandLine, StackAbove(0), CallsAnswered, NoFatalSignal]"] {
        assert!(certificate.contains(statement), "the certificate states `{statement}`");
    }
    let printed = String::from_utf8_lossy(&result.stdout).to_string();
    assert!(!printed.contains("below the stack pointer") && !printed.contains("[checked]"), "and the compile prints no line about the system's stack:\n{printed}");
    assert!(printed.contains("  [presumed]  the stack pointer as the process starts is 0 bytes or more above the data segment's end"), "the command line is above the segment:\n{printed}");
    let (code, out) = run(&binary, b"hello, head\n", Stdio::piped());
    assert_eq!(code, Some(0), "head -c 10 exits 0");
    assert_eq!(out, b"hello, hea", "and has sent the first ten bytes");
    std::fs::remove_dir_all(dir).unwrap();
}

/// A two-header ELF of `code` at 0x400000 (a PT_LOAD of the whole file,
/// readable and executable, and a PT_GNU_STACK asking for a stack that is
/// not), entered at its first byte. `code` gets its own address to patch a
/// pointer with.
fn bare_elf(code: impl Fn(u64) -> Vec<u8>) -> Vec<u8> {
    let entry = 0x400000u64 + 64 + 2 * 56;
    let code = code(entry);
    let total = 64 + 2 * 56 + code.len() as u64;
    let mut file = b"\x7fELF\x02\x01\x01\0\0\0\0\0\0\0\0\0".to_vec();
    for half in [2u16, 62] { file.extend(half.to_le_bytes()); }
    file.extend(1u32.to_le_bytes());
    for word in [entry, 64, 0] { file.extend(word.to_le_bytes()); }
    file.extend(0u32.to_le_bytes());
    for half in [64u16, 56, 2, 0, 0, 0] { file.extend(half.to_le_bytes()); }
    for (kind, flags, words) in [(1u32, 5u32, [0u64, 0x400000, 0x400000, total, total, 0x1000]), (0x6474e551, 6, [0, 0, 0, 0, 0, 16])] {
        file.extend(kind.to_le_bytes());
        file.extend(flags.to_le_bytes());
        for word in words { file.extend(word.to_le_bytes()); }
    }
    file.extend(code);
    file
}

/// `write(1, at, 3)`, and `exit(0)`.
fn write_three(at: u64) -> Vec<u8> {
    let mut code = vec![0xb8, 1, 0, 0, 0, 0xbf, 1, 0, 0, 0, 0x48, 0xbe];
    code.extend(at.to_le_bytes());
    code.extend([0xba, 3, 0, 0, 0, 0x0f, 0x05]);
    code
}
const EXIT_ZERO: [u8; 9] = [0xb8, 60, 0, 0, 0, 0x31, 0xff, 0x0f, 0x05];

/// `binary` run with no environment under a stack limit of `kib` KiB:
/// what it wrote, its exit code, and the signal that ended it.
fn run_under_stack(binary: &Path, kib: u32) -> (Vec<u8>, Option<i32>, Option<i32>) {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new("/bin/sh").env_clear().arg("-c").arg(format!("ulimit -s {kib} && exec \"$0\"")).arg(binary)
        .stdin(Stdio::null()).output().unwrap();
    (out.stdout, out.status.code(), out.status.signal())
}

/// The stack's startup touch against Linux itself
/// (docs/native/system-contract-design.md §3, §4.3). The library's entry code
/// for a room of a MiB (`stack_touched_entry`, the bytes a file on the
/// system's stack starts with), then a line written and exit 0: under a
/// stack limit that leaves the room it prints the line; under one that does
/// not, Linux ends it with SIGSEGV in the entry code and nothing was
/// written. Beside it the room presumed: the line first, then a store a MiB
/// below RSP. Under the small limit that one has printed before it dies,
/// which is the failure the touch removes.
#[test]
fn a_short_stack_ends_a_touched_program_before_any_output() {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["eval", "lib/std/os/linux/linux_x86_64_stack_growth.hthr", "stack_touched_entry(1048576).map(λ (b: BitVec(8)) => b.toNat())", "--limit", "100000"])
        .arg("--cache-dir").arg(showcase::cli_check_images());
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    let result = cmd.output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let printed = String::from_utf8_lossy(&result.stdout).to_string();
    let entry: Vec<u8> = printed.trim().trim_start_matches('[').trim_end_matches(']').split(',').map(|n| n.trim().parse().expect("a byte")).collect();
    // RSP kept and moved below the room, 256 touches of sixteen bytes, RSP
    // put back.
    assert_eq!(entry.len(), 19 + 16 * 256 + 3, "the entry code of a MiB room");
    assert_eq!((&entry[..3], &entry[entry.len() - 6..]), (&[0x48, 0x89, 0xe7][..], &[0x40, 0x88, 0x03, 0x48, 0x89, 0xfc][..]));

    let dir = scratch("touch");
    let touched = dir.join("touched");
    let presumed = dir.join("presumed");
    std::fs::write(&touched, bare_elf(|at| {
        let line = at + (entry.len() + write_three(0).len() + EXIT_ZERO.len()) as u64;
        [&entry[..], &write_three(line), &EXIT_ZERO, b"ok\n"].concat()
    })).unwrap();
    // `mov rbx, rsp; mov rcx, 1 MiB; sub rbx, rcx; mov [rbx], al`.
    let mut deep = vec![0x48, 0x89, 0xe3, 0x48, 0xb9];
    deep.extend(1048576u64.to_le_bytes());
    deep.extend([0x48, 0x29, 0xcb, 0x40, 0x88, 0x03]);
    std::fs::write(&presumed, bare_elf(|at| {
        let line = at + (write_three(0).len() + deep.len() + EXIT_ZERO.len()) as u64;
        [&write_three(line)[..], &deep, &EXIT_ZERO, b"ok\n"].concat()
    })).unwrap();
    for file in [&touched, &presumed] {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(file, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    for file in [&touched, &presumed] {
        assert_eq!(run_under_stack(file, 8192), (b"ok\n".to_vec(), Some(0), None), "with 8 MiB of stack either runs");
    }
    for kib in [1024, 64] {
        assert_eq!(run_under_stack(&touched, kib), (Vec::new(), None, Some(11)), "under {kib} KiB the touched program is ended before it writes");
        assert_eq!(run_under_stack(&presumed, kib), (b"ok\n".to_vec(), None, Some(11)), "under {kib} KiB the presumed one has written when it is ended");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// A program the theorem would not cover is not written, and the refusal
/// says why: past the profile's data limit, a call not compiled, a leaf past the registers
/// with a node too narrow to go a node at a time, a narrow node beside a
/// byte node.
#[test]
fn refused_programs_name_their_reason() {
    let dir = scratch("refused");
    for (source, reason) in [
        ("huge_cat", "`huge_cat` needs a data segment of 2147487744 bytes for its words, buffers, scratch range and saved RSP, past the I/O profile's limit of 1073741824 (`io_data_limit`)"),
        ("stats", "`stats` is refused at statement 1, a call: `stat` is not compiled yet"),
        ("narrow_long_leaf", "`narrow_long_leaf` is refused at statement 1, a computation: the leaf needs 41 registers, one per input and per node, and the pool holds 12; it does not compile a node at a time because a node is not at width 64"),
        ("narrow_mixed_leaf", "`narrow_mixed_leaf` is refused at statement 1, a computation: node 2 of the leaf is not at width 64"),
    ] {
        let output = dir.join(source);
        let result = write_elf(PROBES, source, &output);
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success(), "`{source}` is refused");
        assert!(stderr.contains(reason), "`{source}`'s refusal says `{reason}`:\n{stderr}");
        assert!(!output.exists(), "and nothing is written for it");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
