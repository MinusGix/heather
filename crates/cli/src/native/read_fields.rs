//! The three-field line's formatter (docs/native-wc-design.md §5): the two
//! words of field_line that print a count right-aligned in seven columns,
//! generated at the tail's registers, and the library that tail stands on
//! (`lib/elf64_read_fields.hthr`), which a stream filter's `Fields` finish
//! runs (`read_filter`).
use heather_elab::function_ir_source::generate_elaborated_piece_x86;
use heather_elab::function_ir_x86_lower::{encode_structured, Gpr, Placements};
use heather_elab::Elaborator;

use super::read_loop::FormatPart;

// Bundled after the read profile's and the write loop's: the field
// formatter and the three-field tail.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("field_line", include_str!("../../../../lib/field_line.hthr")),
    ("elf64_read_fields", include_str!("../../../../lib/elf64_read_fields.hthr")),
];

/// The formatter certificates' prefix, as `read_loop::FORMAT_PREFIX`.
pub(super) const FORMAT_PREFIX: &str = "fields_format";

// The formatter's two words at the tail's registers (field_line's `FieldLow`
// and `FieldHigh`): the count in R11, the high word's tail in R10, the word to
// RAX, over the scratch the library fixes for each; R11 and R13–R15 are never
// written.
pub(super) fn generate_format(elab: &Elaborator, prefix: &str) -> Result<Vec<FormatPart>, String> {
    use Gpr::*;
    let parts: [(&str, Placements, Vec<Gpr>); 2] = [
        ("field_low", Placements::from([(0, R11)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R10, R12, Rsi, Rdi, Rbp]),
        ("field_high", Placements::from([(0, R11), (1, R10)]), vec![Rax, Rcx, Rdx, Rbx, R8, R9, R12, Rsi, Rdi, Rbp]),
    ];
    elab.with_module_scope("field_line", |elab| {
        parts.into_iter().map(|(function, inputs, temporaries)| {
            let part = format!("{prefix}_{function}");
            let emission = generate_elaborated_piece_x86(elab, &part, &format!("field_line::{function}"), &inputs, &temporaries, Rax)
                .map_err(|e| format!("{function}: {e:?}"))?;
            Ok(FormatPart { module: format!("{part}_format"), prefix: part, bytes: encode_structured(&emission.lowered), text: emission.text })
        }).collect()
    })?
}
