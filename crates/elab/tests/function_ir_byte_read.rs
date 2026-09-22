#[path = "function_ir_x86.rs"]
mod common;
use heather_elab::function_ir_source::generate_elaborated_read_x86;
use heather_elab::function_ir_x86_lower::{ByteLoad, Gpr, Placements};

fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/data_read.hthr")),
    ] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    }
    elab
}

#[test]
fn byte_read_model_and_typed_body_check() {
    let mut elab = checker();
    let source = "import bitvec; import bool; fn masked(byte, mask: BitVec(8)) → BitVec(8) { @bitvec::BitVec::band(8, byte, mask) } fn less(byte, bound: BitVec(8)) → Bool { @bitvec::BitVec::unsigned_lt_bit(8, byte, bound) } inductive ReadChoice<A> { Keep(value: A), Stop(value: A) } fn choose(byte, bound: BitVec(8)) → ReadChoice<BitVec(8)> { match @bitvec::BitVec::unsigned_lt_bit(8, byte, bound) { True => Keep<BitVec(8)>(byte), False => Stop<BitVec(8)>(bound) } } fn flag(value: Bool) → Bool { value }";
    elab.elab_module_source("read_clients", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let mut native = Vec::new();
    for name in ["masked", "less", "choose"] {
        let outputs = if name == "choose" { Placements::from([(2, Gpr::Rax), (3, Gpr::Rcx)]) } else { Placements::from([(2, Gpr::Rax)]) };
        let emission = generate_elaborated_read_x86(&elab, name, &format!("read_clients::{name}"), 0, Gpr::Rdi,
            &Placements::from([(0, Gpr::Rdx), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rcx, Gpr::R8, Gpr::Rbx, Gpr::R9],
            &outputs).unwrap();
        elab.elab_module_source(&format!("{name}_read"), &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
        if name != "choose" { native.push((name, emission.bytes)); }
    }
    assert!(generate_elaborated_read_x86(&elab, "wrong_type", "read_clients::flag", 0, Gpr::Rdi,
        &Placements::from([(0, Gpr::Rdx)]), &[Gpr::Rax], &Placements::from([(1, Gpr::Rax)])).is_err());
    assert!(generate_elaborated_read_x86(&elab, "wrong_parameter", "read_clients::masked", 99, Gpr::Rdi,
        &Placements::from([(0, Gpr::Rdx), (1, Gpr::Rsi)]), &[Gpr::Rax], &Placements::from([(2, Gpr::Rax)])).is_err());
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    native_clients(&native);
}

#[test]
fn byte_load_canonical_encodings_check() {
    let mut elab = checker();
    let registers = [Gpr::Rax, Gpr::Rcx, Gpr::Rdx, Gpr::Rbx, Gpr::Rsp, Gpr::Rbp, Gpr::Rsi, Gpr::Rdi, Gpr::R8, Gpr::R9, Gpr::R10, Gpr::R11, Gpr::R12, Gpr::R13, Gpr::R14, Gpr::R15];
    let mut assembly = String::from(".text\n");
    let mut expected = Vec::new();
    let mut source = "import x86_64_data_read; import x86_64; import bitvec; import list;".to_string();
    for (i, destination) in registers.iter().enumerate() {
        for (j, base) in registers.iter().enumerate() {
            let load = ByteLoad { destination: *destination, base: *base };
            assembly.push_str(&format!("movzbq (%{}), %{}\n", base.heather_name().to_lowercase(), destination.heather_name().to_lowercase()));
            expected.extend(load.bytes());
            let bytes = load.bytes().iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", ");
            source.push_str(&format!("theorem encoding_{i}_{j}(): ByteLoadDecodes([{bytes}], {}) {{ refl }}\n", load.render()));
        }
    }
    elab.elab_module_source("byte_encodings", &source).unwrap_or_else(|e| panic!("{}", e.render(&source)));
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    assembler_encodings(&assembly, &expected);
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn command(command: &mut std::process::Command) {
    let result = command.output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
}
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn directory(label: &str) -> std::path::PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!("heather-byte-{label}-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&path).unwrap();
    path
}
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn assembler_encodings(assembly: &str, expected: &[u8]) {
    use std::process::Command;
    let dir = directory("encodings");
    std::fs::write(dir.join("loads.s"), assembly).unwrap();
    command(Command::new("as").arg("--64").arg(dir.join("loads.s")).arg("-o").arg(dir.join("loads.o")));
    command(Command::new("objcopy").args(["-O", "binary", "--only-section=.text"]).arg(dir.join("loads.o")).arg(dir.join("loads.bin")));
    assert_eq!(std::fs::read(dir.join("loads.bin")).unwrap(), expected);
    std::fs::remove_dir_all(dir).unwrap();
}
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native_clients(clients: &[(&str, Vec<u8>)]) {
    use std::process::Command;
    let dir = directory("clients");
    let mut assembly = String::from(".text\n");
    for (name, bytes) in clients {
        assembly.push_str(&format!(".globl {name}\n.type {name}, @function\n{name}:\n.byte {}\nret\n", bytes.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(",")));
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    std::fs::write(dir.join("clients.s"), assembly).unwrap();
    std::fs::write(dir.join("main.c"), r#"
#define _GNU_SOURCE
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
extern uint64_t masked(const uint8_t *, uint64_t);
extern uint64_t less(const uint8_t *, uint64_t);
int main(void) {
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0) return 1;
    uint8_t *memory = mmap(0, (size_t)page * 2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (memory == MAP_FAILED || mprotect(memory + page, (size_t)page, PROT_NONE)) return 2;
    uint8_t *last = memory + page - 1;
    for (unsigned byte = 0; byte < 256; ++byte) {
        *last = (uint8_t)byte;
        for (unsigned other = 0; other < 256; ++other) {
            if (masked(last, other) != (byte & other)) return 3;
            if (less(last, other) != (byte < other)) return 4;
            if (*last != byte) return 5;
        }
    }
    return munmap(memory, (size_t)page * 2) != 0;
}
"#).unwrap();
    command(Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"]).arg(dir.join("main.c")).arg(dir.join("clients.s")).arg("-o").arg(dir.join("run")));
    command(&mut Command::new(dir.join("run")));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn byte_read_controls_reject_dishonest_boundaries() {
    let mut elab = checker();
    let imports = "import x86_64_data_read; import x86_64; import bitvec; import bool; import list; import option; import logic;";
    let mut bad_load = ByteLoad { destination: Gpr::Rdx, base: Gpr::Rdi }.bytes();
    bad_load[2] = 0xbe; // MOVSX is not the promised zero-extending load.
    let bytes = bad_load.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", ");
    for (name, declaration) in [
        ("wrong_opcode", format!("theorem bad(): ByteLoadDecodes([{bytes}], ByteLoad(Rdx, Rdi)) {{ refl }}")),
        ("missing_sib", "theorem bad(): ByteLoadDecodes([@bitvec::BitVec::ofNat(8,72), @bitvec::BitVec::ofNat(8,15), @bitvec::BitVec::ofNat(8,182), @bitvec::BitVec::ofNat(8,20)], ByteLoad(Rdx, Rsp)) { refl }".into()),
        ("wrong_value", "theorem bad<M>(byte: BitVec(8), before: MachineState<M>): read_gpr(Rdx, byte_load_after(ByteLoad(Rdx, Rdi), byte, before).gprs) = @bitvec::BitVec::zero(64) { byte_load_result(ByteLoad(Rdx, Rdi), byte, before) }".into()),
        ("wrong_frame", "theorem bad<M>(byte: BitVec(8), before: MachineState<M>): read_gpr(Rdx, byte_load_after(ByteLoad(Rdx, Rdi), byte, before).gprs) = read_gpr(Rdx, before.gprs) { byte_load_preserves(ByteLoad(Rdx, Rdi), byte, before, Rdx, refl) }".into()),
        ("denied_read", "theorem bad<M>(byte: BitVec(8), before: MachineState<M>, canonical: bitvec::BitVec::drop_low(47,17,read_gpr(Rdi,before.gprs)) = @bitvec::BitVec::zero(17)): ByteLoadStep<M>(ByteReadAccess<M>(λ memory address => None), ByteLoad(Rdx,Rdi), byte, before, byte_load_after(ByteLoad(Rdx,Rdi),byte,before)) { ByteLoadStep(canonical := canonical, present := refl, execution := refl) }".into()),
        ("noncanonical_read", "theorem bad<M>(memory: M): ByteLoadStep<M>(ByteReadAccess<M>(λ memory address => Some(@bitvec::BitVec::ofNat(8,7))), ByteLoad(Rdx,Rdi), @bitvec::BitVec::ofNat(8,7), MachineState(write_gpr(Rdi,@bitvec::BitVec::ofNat(64,140737488355328),zero_gprs()),clear_flags(),@bitvec::BitVec::zero(64),memory), byte_load_after(ByteLoad(Rdx,Rdi),@bitvec::BitVec::ofNat(8,7),MachineState(write_gpr(Rdi,@bitvec::BitVec::ofNat(64,140737488355328),zero_gprs()),clear_flags(),@bitvec::BitVec::zero(64),memory))) { ByteLoadStep(canonical := refl, present := refl, execution := refl) }".into()),
        ("wrong_address", "theorem bad<M>(access: ByteReadAccess<M>, byte: BitVec(8), before: MachineState<M>, canonical: bitvec::BitVec::drop_low(47,17,read_gpr(Rdi,before.gprs)) = @bitvec::BitVec::zero(17), present: access.read(before.memory,read_gpr(Rsi,before.gprs)) = Some(byte)): ByteLoadStep<M>(access,ByteLoad(Rdx,Rdi),byte,before,byte_load_after(ByteLoad(Rdx,Rdi),byte,before)) { ByteLoadStep(canonical := canonical, present := present, execution := refl) }".into()),
    ] {
        let source = format!("{imports} {declaration}");
        heather_syntax::parse_file(&source).unwrap();
        let error = elab.elab_module_source(name, &source).expect_err("dishonest byte-load claim must fail");
        let message = error.render(&source);
        assert!(!message.contains("unknown") && !message.contains("not in scope") && !message.contains("cannot infer") && !message.contains("takes value parameters"), "{name}: {message}");
    }
}
