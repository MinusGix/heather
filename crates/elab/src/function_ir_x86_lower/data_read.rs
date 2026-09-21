//! Canonical MOVZX r64, byte [base] plan; semantics live in x86_64_data_read.
use super::Gpr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteLoad {
    pub destination: Gpr,
    pub base: Gpr,
}
impl ByteLoad {
    pub fn bytes(self) -> Vec<u8> {
        let destination = super::register_code(self.destination);
        let base = super::register_code(self.base);
        let displaced = base & 7 == 5;
        let mut bytes = vec![0x48 | ((destination >> 3) << 2) | (base >> 3), 0x0f, 0xb6,
            (if displaced { 0x40 } else { 0 }) | ((destination & 7) << 3) | (base & 7)];
        if base & 7 == 4 { bytes.push(0x24); }
        if displaced { bytes.push(0); }
        bytes
    }
    pub fn render(self) -> String {
        format!("ByteLoad(destination := {}, base := {})", self.destination.heather_name(), self.base.heather_name())
    }
}
