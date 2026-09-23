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
impl AccessFragment {
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
        let r = register_code(register);
        let mut bytes = vec![0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7), 0x74, fd as u8];
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
