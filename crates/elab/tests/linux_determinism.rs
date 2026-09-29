use crate::read_loop_fixture::checker;

// The run is the run (docs/fetched-step-determinism-design.md): every step
// form reads back from the front of its bytes, so a step is a function of
// the defined state and none runs at a SYSCALL; a claimed run is then every
// run that got the same answers from Linux.
const FORMS: &str = include_str!("../../../lib/std/arch/x86_64/x86_64_step_forms.hthr");
const DETERMINISM: &str = include_str!("../../../lib/linux_x86_64_determinism.hthr");

#[test]
fn claimed_runs_are_every_run() {
    let mut elab = checker();
    elab.elab_module_source("x86_64_step_forms", FORMS).unwrap_or_else(|e| panic!("{}", e.render(FORMS)));
    elab.elab_module_source("linux_x86_64_determinism", DETERMINISM).unwrap_or_else(|e| panic!("{}", e.render(DETERMINISM)));
}

// Each change is refused where it is wrong, not by a missing name: a decoder
// that reads ADD as SUB, takes a store for a register form, or looks for
// SYSCALL at another opcode is not complete on the forms; a run in which a
// failed read may leave more junk than it asked for, or whose answers are
// compared by kind alone, is not the claimed run.
#[test]
fn determinism_refusals() {
    let library = checker().semantic_image();
    for (name, from, to) in [
        ("add_read_as_sub", "Inl(_) => emitted_form(AddRR(rm, reg)),", "Inl(_) => emitted_form(SubRR(rm, reg)),"),
        ("store_read_as_register", "Cons(modrm, _) => match byte_bit7(modrm) {", "Cons(modrm, _) => match !byte_bit7(modrm) {"),
        ("syscall_elsewhere", "match opcode.eq_dec(BitVec::ofNat(0x05)) {", "match opcode.eq_dec(BitVec::ofNat(0x06)) {"),
    ] {
        let bad = FORMS.replacen(from, to, 1);
        assert_ne!(bad, FORMS, "{name}");
        let error = library.elaborator().elab_module_source("x86_64_step_forms", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
    let mut elab = library.elaborator();
    elab.elab_module_source("x86_64_step_forms", FORMS).unwrap_or_else(|e| panic!("{}", e.render(FORMS)));
    let forms = elab.semantic_image();
    for (name, from, to) in [
        ("junk_unbounded", "(junk.len() <= read_gpr(Rdx, at.gprs).toNat()) ∧\n", "True ∧\n"),
        ("answers_by_kind", "ReadEvent(_, other) => result = other,", "ReadEvent(_, other) => True,"),
    ] {
        let bad = DETERMINISM.replacen(from, to, 1);
        assert_ne!(bad, DETERMINISM, "{name}");
        let error = forms.elaborator().elab_module_source("linux_x86_64_determinism", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
