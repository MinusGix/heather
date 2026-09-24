//! Untrusted composition proposals over existing pure certificates and reads.
//! Publication checks literal bytes and branch targets in the kernel.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccessFragment {
    pub bytes: Vec<u8>,
    code: String,
    layout: String,
    imports: BTreeSet<String>,
}
/// TEST r64, r64 on one register: the selector every access edge reads.
fn test_bytes(register: Gpr) -> [u8; 3] {
    let r = register_code(register);
    [0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7)]
}

/// A loop's exit displacement (past the body, its TEST and the back edge),
/// the offset where the back edge starts, and the back displacement, which
/// with that offset and the edge's own six bytes completes a 2^32 orbit.
pub fn near_loop_edges(guard: usize, body: usize) -> Result<(usize, usize, u64), String> {
    let exit = body + 9;
    let back_from = guard + 9 + body + 3;
    let span = back_from + 6;
    if exit > i32::MAX as usize || span > i32::MAX as usize { return Err("loop exceeds the near-branch range".into()); }
    Ok((exit, back_from, (1u64 << 32) - span as u64))
}

impl AccessFragment {
    /// The `AccessCode` term this fragment publishes, for proofs that name
    /// its subtrees.
    pub fn code(&self) -> &str { &self.code }
    /// The named structured certificate declarations must be in scope when
    /// checking publication. A mismatched plan/name fails the encoding proof.
    pub fn structured(prefix: &str, plan: &LoweredStructured) -> Self {
        Self { imports: prefix.rsplit_once("::").map(|(module, _)| module.to_string()).into_iter().collect(), bytes: encode_structured(plan), code: format!("AccessPure({prefix}_code())"), layout: format!("{prefix}_layout()") }
    }
    pub fn read(load: ByteLoad) -> Self {
        Self { imports: BTreeSet::new(), bytes: load.bytes(), code: format!("AccessRead({})", load.render()), layout: "trivial".into() }
    }
    pub fn sequence(self, tail: Self) -> Self {
        let mut bytes = self.bytes;
        bytes.extend(tail.bytes);
        let imports = self.imports.union(&tail.imports).cloned().collect();
        Self { imports, bytes, code: format!("AccessSequence({}, {})", self.code, tail.code),
            layout: format!("access_sequence_layout({}, {}, {}, {})", self.code, tail.code, self.layout, tail.layout) }
    }
    /// Resolve both forward labels from child byte lengths. Larger spans
    /// decline explicitly until near-branch selection is available.
    pub fn branch(register: Gpr, yes: Self, no: Self) -> Result<Self, String> {
        let fd = yes.bytes.len().checked_add(2).filter(|n| *n <= 127).ok_or("access true arm exceeds short-branch range")?;
        let jd = no.bytes.len();
        if jd > 127 { return Err("access false arm exceeds short-branch range".into()); }
        let mut bytes = test_bytes(register).to_vec();
        bytes.extend([0x74, fd as u8]);
        bytes.extend(yes.bytes);
        bytes.extend([0xeb, jd as u8]);
        bytes.extend(no.bytes);
        let target = |d| format!("λ (start: BitVec(64)) => trans(sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2), @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {d})))), bitvec::BitVec::iterate_increment_compose(64, start, 2, {d}))");
        let imports = yes.imports.union(&no.imports).cloned().collect();
        // Through the library lemmas, not a tuple against AccessLayout of the
        // literal tree: the tuple makes the elaborator spell the tree's reduct.
        let displacements = format!("@bitvec::BitVec::ofNat(8, {fd}), @bitvec::BitVec::ofNat(8, {jd})");
        Ok(Self { imports, bytes,
            code: format!("AccessBranch({}, {displacements}, {}, {})", register.heather_name(), yes.code, no.code),
            layout: format!("access_branch_layout({}, {displacements}, {}, {}, {}, {}, {}, {})",
                register.heather_name(), yes.code, no.code, target(fd), target(jd), yes.layout, no.layout),
        })
    }
    /// A bounded loop (docs/native-bounded-loops-design.md §3): the guard, a
    /// near exit edge over the body, the body, and a near back edge to the
    /// guard. Both displacements are resolved from child lengths here and
    /// checked in the kernel by the layout proof.
    pub fn looped(guard: Self, flag: Gpr, body: Self, step: Gpr) -> Result<Self, String> {
        let (exit, back_from, back) = near_loop_edges(guard.bytes.len(), body.bytes.len())?;
        let mut bytes = guard.bytes.clone();
        bytes.extend(test_bytes(flag));
        bytes.extend([0x0f, 0x84]);
        bytes.extend((exit as u32).to_le_bytes());
        bytes.extend(&body.bytes);
        bytes.extend(test_bytes(step));
        bytes.extend([0x0f, 0x84]);
        bytes.extend((back as u32).to_le_bytes());
        let imports = guard.imports.union(&body.imports).cloned().collect();
        let exit_d = format!("@bitvec::BitVec::ofNat(32, {exit})");
        let back_d = format!("@bitvec::BitVec::ofNat(32, {back})");
        let code = format!("AccessLoop({}, {}, {exit_d}, {}, {}, {back_d})", guard.code, flag.heather_name(), body.code, step.heather_name());
        let layout = format!("access_loop_layout({}, {}, {exit_d}, {}, {}, {back_d}, \
            λ (start: BitVec(64)) => near_branch_forward(start, 6, {exit}, {exit_d}, refl), \
            λ (start: BitVec(64)) => near_branch_returns(start, {back_from}, 6, {back_d}, refl), {}, {})",
            guard.code, flag.heather_name(), body.code, step.heather_name(), guard.layout, body.layout);
        Ok(Self { imports, bytes, code, layout })
    }
    pub fn publish(&self, prefix: &str) -> String {
        let mut module = Module::default();
        module.raw("import x86_64_access_code; import x86_64; import x86_64_block; import bitvec; import list; import logic;");
        for name in &self.imports { module.raw(format!("import {name};")); }
        module.declaration(emitted_function(format!("{prefix}_code"), false, vec![], "AccessCode", &self.code));
        let bytes = self.bytes.iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect::<Vec<_>>().join(", ");
        module.declaration(emitted_function(format!("{prefix}_bytes"), false, vec![], "List<BitVec(8)>", format!("[{bytes}]")));
        module.declaration(emitted_theorem(format!("{prefix}_encoding"), false, vec![], format!("{prefix}_bytes() = access_bytes({prefix}_code())"), "refl"));
        module.declaration(emitted_theorem(format!("{prefix}_layout"), false, vec![], format!("AccessLayout({prefix}_code())"), &self.layout));
        module.render()
    }
}
