use crate::common;
use heather_elab::function_ir_source::{generate_elaborated_typed_x86, generate_elaborated_read_x86};
use heather_elab::function_ir_x86_lower::{AccessFragment, Gpr, Placements};

#[test]
fn selected_bounds_read_checks_and_executes() {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
        ("x86_64_access_code", include_str!("../../../lib/std/arch/x86_64/x86_64_access_code.hthr")),
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/bitvec_nat.hthr")),
        ("function_ir_loop", include_str!("../../../lib/function_ir_loop.hthr")),
        ("function_ir_loop_x86", include_str!("../../../lib/function_ir_loop_x86.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    let source = "import bitvec; import bool; fn bounds(cursor, length: BitVec(64)) → Bool { @bitvec::BitVec::unsigned_lt_bit(64, cursor, length) } fn address(base, cursor: BitVec(64)) → BitVec(64) { @bitvec::BitVec::add(64, base, cursor) } fn identity(byte: BitVec(8)) → BitVec(8) { byte } fn masked(byte, mask: BitVec(8)) → BitVec(8) { @bitvec::BitVec::band(8, byte, mask) } fn zero() → BitVec(8) { @bitvec::BitVec::ofNat(8, 0) }";
    elab.elab_module_source("clients", source).unwrap();
    let guard = generate_elaborated_typed_x86(&elab, "guard", "clients::bounds",
        &Placements::from([(0,Gpr::Rsi),(1,Gpr::Rdx)]), &[Gpr::Rax,Gpr::R10], &Placements::from([(2,Gpr::Rax)])).unwrap();
    let address = generate_elaborated_typed_x86(&elab, "address", "clients::address",
        &Placements::from([(0,Gpr::Rdi),(1,Gpr::Rsi)]), &[Gpr::R8], &Placements::from([(2,Gpr::R8)])).unwrap();
    let zero = generate_elaborated_typed_x86(&elab, "zero", "clients::zero",
        &Placements::new(), &[Gpr::Rax], &Placements::from([(0,Gpr::Rax)])).unwrap();
    let declarations = stitch(&format!("{}\n{}\n{}", guard.text, address.text, zero.text));
    eprintln!("checking selected pure prefixes");
    elab.elab_module_source("prefixes", &declarations).unwrap_or_else(|e| panic!("{}", e.render(&declarations)));
    let mut natives = Vec::new();
    let mut consumer = String::new();
    for name in ["identity", "masked"] {
        elab.elab_module_source("select_client", "import clients; import bitvec; import bool; import nat;").unwrap();
        let inputs = if name == "identity" { Placements::from([(0,Gpr::R9)]) } else { Placements::from([(0,Gpr::R9),(1,Gpr::Rcx)]) };
        let output = if name == "identity" {1} else {2};
        let read = generate_elaborated_read_x86(&elab, name, &format!("clients::{name}"), 0, Gpr::R8,
            &inputs, &[Gpr::Rax,Gpr::R10], &Placements::from([(output,Gpr::Rax)])).unwrap();
        elab.elab_module_source(&format!("{name}_body"), &read.text).unwrap_or_else(|e| panic!("{}", e.render(&read.text)));
        let yes = AccessFragment::structured("prefixes::address", &address.lowered).sequence(
            AccessFragment::read(read.load).sequence(AccessFragment::structured(&format!("{name}_body::{name}_body"), &read.body)));
        let no = AccessFragment::structured("prefixes::zero", &zero.lowered);
        let mut long = yes.clone();
        while long.bytes.len() <= 127 { long = long.sequence(yes.clone()); }
        assert!(AccessFragment::branch(Gpr::Rax, long.clone(), no.clone()).is_err());
        assert!(AccessFragment::branch(Gpr::Rax, yes.clone(), long).is_err());
        let branch = AccessFragment::branch(Gpr::Rax, yes.clone(), no).unwrap();
        if name == "identity" {
            consumer = include_str!("fixtures/guarded_read_consumer.hthr.in")
                .replace("$FD", &branch.bytes[4].to_string()).replace("$JD", &zero.lowered.byte_length.to_string());
        }
        let whole = AccessFragment::structured("prefixes::guard", &guard.lowered).sequence(branch.clone());
        let text = stitch(&format!("{}\n{}\n{}", yes.publish("yes"), branch.publish("branch"), whole.publish("whole")));
        eprintln!("checking {name} access publication");
        elab.elab_module_source(&format!("{name}_selected"), &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
        let mut corrupt = whole.clone();
        corrupt.bytes[guard.lowered.byte_length + 4] ^= 1;
        let bad = corrupt.publish("bad");
        assert!(elab.semantic_image().elaborator().elab_module_source("bad_target", &bad).is_err());
        natives.push((name, whole.bytes));
    }
    eprintln!("checking open guard/read consumer");
    elab.elab_module_source("consumer", &consumer).unwrap_or_else(|e| panic!("{}", e.render(&consumer)));
    for (name, from, to) in [
        ("wrong_guard", "ended: nat::Nat::leb(length, cursor) = True", "ended: nat::Nat::leb(length, cursor) = False"),
        ("wrong_address", "address_typed_correct(base_word, cursor_word", "address_typed_correct(cursor_word, base_word"),
        ("wrong_byte", "identity_read_artifact(byte, access", "identity_read_artifact(@bitvec::BitVec::zero(8), access"),
    ] {
        let bad = consumer.replace(from, to);
        assert_ne!(bad, consumer);
        assert!(heather_syntax::parse_file(&bad).is_ok());
        let error = elab.semantic_image().elaborator().elab_module_source(name, &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
    }
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    native(&natives);
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native(clients: &[(&str, Vec<u8>)]) {
    use std::process::Command;
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = std::env::temp_dir().join(format!("heather-guarded-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let mut assembly = String::from(".text\n");
    for (name, bytes) in clients {
        assembly.push_str(&format!(".global {name}\n{name}:\n.byte {}\nret\n", bytes.iter().map(u8::to_string).collect::<Vec<_>>().join(",")));
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    std::fs::write(dir.join("code.s"), assembly).unwrap();
    std::fs::write(dir.join("driver.c"), r#"
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
#include <assert.h>
extern uint64_t identity(const uint8_t*, uint64_t, uint64_t, uint64_t);
extern uint64_t masked(const uint8_t*, uint64_t, uint64_t, uint64_t);
int main(void) {
    long page = sysconf(_SC_PAGESIZE);
    uint8_t *p = mmap(0, page*2, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    assert(p != MAP_FAILED);
    assert(mprotect(p+page, page, PROT_NONE) == 0);
    for (unsigned b=0; b<256; b++) {
        p[page-1] = b;
        for (unsigned mask=0; mask<256; mask++) {
            assert(identity(p, page-1, page, mask) == b);
            assert(masked(p, page-1, page, mask) == (b & mask));
            assert(masked(p, page, page, mask) == 0);
            assert(p[page-1] == b);
        }
    }
    const uint64_t edges[] = {0, 1, UINT64_C(1)<<63, UINT64_MAX};
    for (unsigned i=0;i<4;i++) for (unsigned j=0;j<=i;j++) {
        // Denied address is safe only because cursor >= length skips the read.
        assert(identity(p+page, edges[i], edges[j], 0) == 0);
        assert(masked(p+page, edges[i], edges[j], 255) == 0);
    }
    assert(munmap(p, page*2) == 0);
}
"#).unwrap();
    let output = Command::new("cc").args(["-Wall","-Wextra","-Werror"]).arg(dir.join("driver.c")).arg(dir.join("code.s")).arg("-o").arg(dir.join("run")).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(Command::new(dir.join("run")).status().unwrap().success());
    std::fs::remove_dir_all(dir).unwrap();
}

fn stitch(text: &str) -> String {
    let mut imports = std::collections::BTreeSet::new();
    let mut body = String::new();
    for line in text.lines() {
        if line.starts_with("import ") { imports.insert(line); }
        else { body.push_str(line); body.push('\n'); }
    }
    format!("{}\n{body}", imports.into_iter().collect::<Vec<_>>().join("\n"))
}
