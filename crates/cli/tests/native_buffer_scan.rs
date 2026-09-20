//! Native bounded iteration, independent decimal interpretation, and refusals.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::path::Path;
use std::process::Command;
#[path = "../src/native/support.rs"] mod support;

#[test]
fn slow_acceptance_buffer_scan_runtime_and_refusals() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-buffer-scan-{}-{nonce}",std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let compile = |source:&Path, symbol:&str, output:&Path| Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .arg("compile-x86").arg(source).arg(symbol).args(["--buffer-scan","--cache-dir","target/native-test-images","-o"]).arg(output).output().unwrap();
    let asm = dir.join("decimal.s");
    let built = compile(Path::new("examples/x86-native/decimal_step.hthr"),"decimal_step",&asm);
    assert!(built.status.success(),"{}",String::from_utf8_lossy(&built.stderr));
    assert!(String::from_utf8_lossy(&built.stdout).contains("full machine-loop refinement"));
    let exe = dir.join("decimal");
    let linked = Command::new("cc").current_dir(&root).args(["-std=c11","-Wall","-Wextra","-Werror","examples/x86-native/decimal_main.c","examples/x86-native/scan_abi.S"])
        .arg(&asm).arg("-o").arg(&exe).output().unwrap();
    assert!(linked.status.success(),"{}",String::from_utf8_lossy(&linked.stderr));
    for (input,cursor,expected) in [
        ("123+4","0","ok 123 3\n"), ("x123+4","1","ok 123 4\n"),
        ("","0","no-digits 0 0\n"), ("x","0","no-digits 0 0\n"),
        ("0","0","ok 0 1\n"), ("000123","0","ok 123 6\n"),
        ("18446744073709551615","0","ok 18446744073709551615 20\n"),
        ("18446744073709551616","0","overflow 1844674407370955161 19\n"),
        ("99999999999999999999","0","overflow 9999999999999999999 19\n"),
        ("123","3","no-digits 0 3\n"), ("123","18446744073709551615","no-digits 0 18446744073709551615\n"),
    ] {
        let output = Command::new(&exe).args([input,cursor]).output().unwrap();
        assert!(output.status.success()); assert_eq!(String::from_utf8_lossy(&output.stdout),expected);
    }
    assert_eq!(Command::new(&exe).arg("0".repeat(256)).output().unwrap().stdout,b"ok 0 256\n");
    assert_eq!(Command::new(&exe).arg("0".repeat(257)).status().unwrap().code(),Some(65));
    let harness = dir.join("oracle.c");
    std::fs::write(&harness,r#"
#define _GNU_SOURCE
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
struct reply { uint64_t status, value, next; };
extern struct reply scan_buffer(const unsigned char *, uint64_t, uint64_t);
static struct reply reference(const unsigned char *s, uint64_t n, uint64_t p) {
    struct reply r = { 1, 0, p };
    unsigned count = 0;
    while (r.next < n) {
        if (count == 256) { r.status = 3; return r; }
        unsigned byte = s[r.next];
        if (byte < '0' || byte > '9') return r;
        __uint128_t natural = (__uint128_t)r.value * 10 + byte - '0';
        if (natural > UINT64_MAX) { r.status = 2; return r; }
        r.value = (uint64_t)natural; ++r.next; ++count; r.status = 0;
    }
    return r;
}
static int check(const unsigned char *s, uint64_t n, uint64_t p) {
    struct reply a = scan_buffer(s,n,p), b = reference(s,n,p);
    return a.status != b.status || a.value != b.value || a.next != b.next;
}
int main(void) {
    unsigned char data[257], saved[257];
    for (unsigned byte = 0; byte < 256; ++byte) {
        memset(data,(int)byte,sizeof data); memcpy(saved,data,sizeof data);
        for (unsigned p = 0; p <= 256; ++p) if (check(data,256,p)) return 1;
        if (memcmp(data,saved,sizeof data)) return 2;
    }
    uint64_t seed = 0x123456789abcdef;
    for (unsigned run = 0; run < 10000; ++run) {
        for (unsigned i = 0; i < sizeof data; ++i) {
            seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
            data[i] = run % 2 ? (unsigned char)('0' + seed % 10) : (unsigned char)(seed % 256);
        }
        if (check(data,run % 258,run % 23)) return 3;
    }
    memset(data,'0',sizeof data);
    if (check(data,257,0)) return 4;
    long page = sysconf(_SC_PAGESIZE);
    if (page < 256) return 5;
    unsigned char *m = mmap(0,(size_t)page*2,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if (m == MAP_FAILED || mprotect(m+page,(size_t)page,PROT_NONE)) return 6;
    memset(m+page-256,'0',256);
    if (check(m+page-256,256,0)) return 7;
    struct reply limited = scan_buffer(m+page-256,257,0);
    if (limited.status != 3 || limited.value || limited.next != 256) return 8;
    if (check(m+page,0,0) || check(0,0,UINT64_MAX)) return 9;
    m[page-1] = '7'; if (check(m+page-1,1,0)) return 10;
    return munmap(m,(size_t)page*2) ? 11 : 0;
}
"#).unwrap();
    let oracle = dir.join("oracle");
    let result = Command::new("cc").current_dir(&root).args(["-std=c11","-Wall","-Wextra","-Werror"])
        .arg(&harness).arg("examples/x86-native/scan_abi.S").arg(&asm).arg("-o").arg(&oracle).output().unwrap();
    assert!(result.status.success(),"{}",String::from_utf8_lossy(&result.stderr));
    assert!(Command::new(&oracle).status().unwrap().success());
    // The same compiler and loop handle a non-decimal source body.
    let spaces = dir.join("spaces.s");
    let result = compile(Path::new("examples/x86-native/count_spaces.hthr"),"count_spaces",&spaces);
    assert!(result.status.success(),"{}",String::from_utf8_lossy(&result.stderr));
    let spaces_exe = dir.join("spaces");
    let result = Command::new("cc").current_dir(&root).args(["-DSCANNER=count_spaces","examples/x86-native/decimal_main.c","examples/x86-native/scan_abi.S"])
        .arg(&spaces).arg("-o").arg(&spaces_exe).output().unwrap();
    assert!(result.status.success());
    assert_eq!(Command::new(&spaces_exe).arg("   x").output().unwrap().stdout,b"ok 3 3\n");
    // Standalone certificate replay, then mutations at each checked boundary.
    for &(name,source) in support::SUPPORT.iter().chain(support::SCAN_SUPPORT) {
        std::fs::write(dir.join(format!("{name}.hthr")),source).unwrap();
    }
    let source = include_str!("../../../examples/x86-native/decimal_step.hthr");
    std::fs::write(dir.join("decimal_step.hthr"),source).unwrap();
    let certificate = std::fs::read_to_string(dir.join("decimal.certificate.hthr")).unwrap();
    let check = |name:&str,text:&str,accepted:bool| check_certificate(&root,&dir,name,text,accepted);
    check("replay",&certificate,true);
    let mutate = |name:&str,needle:&str,replacement:&str| {
        assert!(certificate.contains(needle),"missing mutation target {needle}");
        check(name,&certificate.replacen(needle,replacement,1),false);
    };
    mutate("wrong_load_encoding","Cons(elf_byte(75), decimal_step_native_head_from_58())","Cons(elf_byte(74), decimal_step_native_head_from_58())");
    mutate("wrong_outcome","{ ScanStop }","{ ScanOverflow }");
    mutate("wrong_bounds_branch","Cons(elf_byte(131), decimal_step_native_head_from_34())","Cons(elf_byte(130), decimal_step_native_head_from_34())");
    mutate("wrong_fuel_branch","Cons(elf_byte(132), decimal_step_native_head_from_53())","Cons(elf_byte(133), decimal_step_native_head_from_53())");
    // Keep the accepted RIP theorem symbolic. Refuse its wrong-offset control
    // at a concrete code base: normalizing two unequal 33-deep symbolic
    // increments would measure conversion fuel rather than the address error.
    let target = certificate.lines().find(|line| line.starts_with("theorem decimal_step_native_body_entry_target")).unwrap();
    let concrete = target.replace("before.rip", "bitvec::zero(64)")
        .replace("before)", "with_rip(before, bitvec::zero(64)))");
    let target_imports = "import x86_64_scan_gate; import x86_64_scan_body; import x86_64_buffer_cursor; import x86_64; import x86_64_block; import bitvec; import bool;\n";
    check("concrete_body_entry_rip",&format!("{target_imports}{concrete}"),true);
    check("wrong_body_entry_rip",&format!("{target_imports}{}",concrete.replace("next_rip(bitvec::zero(64), 33)","next_rip(bitvec::zero(64), 32)")),false);
    let boundary = certificate.find("theorem decimal_step_native_body_correct").unwrap();
    let mut wrong_scope = certificate[..boundary].to_string();
    wrong_scope.push_str(&certificate[boundary..].replacen("read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs))", "read_gpr(Rsi, before.gprs), read_gpr(Rsi, before.gprs))",1));
    check("wrong_byte_scope",&wrong_scope,false);
    let start = certificate.find("ScanNext([").unwrap();
    let end = start + certificate[start..].find("]) }").unwrap();
    // Check the frame at its own boundary. A changed instruction count also
    // invalidates downstream semantic/layout proofs; those are separate
    // controls, and attempting all stale proofs can merely exhaust fuel.
    let node_start = certificate[..start].rfind("fn ").unwrap();
    let node_name = certificate[node_start+3..].split('(').next().unwrap();
    let frame_start = certificate.find(&format!("theorem {node_name}_frame")).unwrap();
    let frame_end = frame_start + certificate[frame_start..].find('\n').unwrap();
    let mut clobbered = certificate[..end].to_string();
    clobbered.push_str(", MovRI(R10, bitvec::zero(64))]) }\n");
    clobbered.push_str(&certificate[frame_start..frame_end]);
    check("clobbered_cursor",&clobbered,false);
    mutate("wrong_initial_accumulator","cursor, bitvec::zero(64), False)","cursor, bitvec::ofNat(64, 1), False)");
    std::fs::write(dir.join("decimal_step.hthr"),source.replace("bitvec::ofNat(64, 54)","bitvec::ofNat(64, 53)")).unwrap();
    check("stale_source",&certificate,false);
    let model_path = dir.join("byte_scan.hthr");
    let model = std::fs::read_to_string(&model_path).unwrap();
    std::fs::write(&model_path,model.replacen("bitvec::ofNat(64, 3)","bitvec::ofNat(64, 4)",1)).unwrap();
    let replaced_output = dir.join("replaced_model.s");
    let result = compile(&dir.join("decimal_step.hthr"),"decimal_step",&replaced_output);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("differs from the compiler's bundled proof library"));
    assert!(!replaced_output.exists() && !replaced_output.with_extension("certificate.hthr").exists());
    std::fs::write(&model_path,model).unwrap();
    // Alias growth is refused before an exponential expression is built.
    let mut explosive = String::from("import bitvec; import byte_scan; fn explode(byte, value: BitVec(64)) -> ScanStep { let x0 = byte; ");
    for i in 1..24 { explosive.push_str(&format!("let x{i} = bitvec::add(64, x{}, x{}); ",i-1,i-1)); }
    explosive.push_str("Next(x23) }");
    let path = dir.join("explode.hthr"); std::fs::write(&path,explosive).unwrap();
    let output = dir.join("explode.s"); let result = compile(&path,"explode",&output);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("256-node source limit"),"{}",String::from_utf8_lossy(&result.stderr));
    assert!(!output.exists() && !output.with_extension("certificate.hthr").exists());
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn slow_acceptance_buffer_scan_gate_permissions_and_paths() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-scan-gate-{}-{nonce}",std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for &(name,source) in support::SUPPORT.iter().chain(support::SCAN_SUPPORT) {
        std::fs::write(dir.join(format!("{name}.hthr")),source).unwrap();
    }
    let check = |name:&str,text:&str,accepted:bool| check_certificate(&root,&dir,name,text,accepted);
    // Open memory and registers: permissions cannot be manufactured by reducing
    // a concrete memory image, and each premise is independently necessary.
    let permission = r#"
import x86_64_scan_gate; import x86_64_buffer_cursor; import x86_64_calls;
import x86_64; import bitvec; import bool; import logic;
theorem load_permission<M>(access: BufferAccess<M>, before: MachineState<M>,
    canonical: LowCanonical(scan_address(before)),
    no_wrap: bitvec::carry_add_bit(64, read_gpr(R8, before.gprs), read_gpr(R10, before.gprs)) = False,
    readable: access.readable(scan_address(before)) = True):
    ExecuteScanLoad(access, before, scan_load(access, before)) {
    ⟨ScanReadAllowed(canonical, no_wrap, readable), refl⟩
}
"#;
    check("load_permission",permission,true);
    for (name,arguments) in [
        ("missing_read_permission","canonical, no_wrap, refl"),
        ("missing_no_wrap","canonical, refl, readable"),
        ("missing_canonical","refl, no_wrap, readable"),
    ] { check(name,&permission.replace("ScanReadAllowed(canonical, no_wrap, readable)",&format!("ScanReadAllowed({arguments})")),false); }
    let paths = r#"
import x86_64_scan_gate; import x86_64_buffer_cursor; import x86_64;
import bitvec; import bool; import logic;
theorem no_read_on_end<M>(access: BufferAccess<M>, done, limit: BitVec(32), before: MachineState<M>,
    outside: scan_bounds(before) = False):
    scan_gate(access, done, limit, before) = ScanEnd(scan_bounds_edge(False, done, before)) {
    scan_gate_end(access, done, limit, before, outside)
}
theorem no_read_on_limit<M>(access: BufferAccess<M>, done, limit: BitVec(32), before: MachineState<M>,
    inside: scan_bounds(before) = True, empty: scan_empty_fuel(before) = True):
    scan_gate(access, done, limit, before) = ScanLimit(scan_fuel_edge(True, limit, scan_bounds_edge(True, done, before))) {
    scan_gate_limit(access, done, limit, before, inside, empty)
}
theorem selected_byte<M>(access: BufferAccess<M>, done, limit: BitVec(32), before: MachineState<M>):
    read_gpr(Rdi, (scan_load(access, scan_fuel_edge(False, limit, scan_bounds_edge(True, done, before)))).gprs) =
        bitvec::zero_extend(8, 56, access.read(before.memory, scan_address(before))) {
    scan_ready_byte(access, done, limit, before)
}
"#;
    check("guard_paths",paths,true);
    check("inverted_bounds",&paths.replace("outside: scan_bounds(before) = False","outside: scan_bounds(before) = True"),false);
    check("inverted_fuel",&paths.replace("empty: scan_empty_fuel(before) = True","empty: scan_empty_fuel(before) = False"),false);
    check("wrong_load_address",&paths.replace("access.read(before.memory, scan_address(before))","access.read(before.memory, read_gpr(R8, before.gprs))"),false);

    std::fs::remove_dir_all(&dir).unwrap();
}

fn check_certificate(root:&Path, dir:&Path, name:&str, text:&str, accepted:bool) {
    let path = dir.join(format!("{name}.hthr")); std::fs::write(&path,text).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root).arg("check").arg(&path)
        .args(["--cache","--cache-dir","target/native-test-images"]).output().unwrap();
    let error = String::from_utf8_lossy(&result.stderr);
    assert_eq!(result.status.success(),accepted,"{name}: {error}");
    if !accepted { assert!(!error.contains("OutOfFuel"),"{name}: {error}"); assert!(error.contains("NotConvertible") || error.contains("this has type"),"{name}: {error}"); }
}
