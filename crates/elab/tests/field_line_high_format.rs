use crate::field_line_format::word_certifies;

// field_line_format's check for the high word, in a process of its own.
#[test]
fn field_high_certifies() { word_certifies("field_high"); }
