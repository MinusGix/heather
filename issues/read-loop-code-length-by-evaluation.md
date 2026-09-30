---
title: The read-loop and print profiles measure their code by evaluating it
status: closed
labels: [native,elaboration]
created: 2026-09-29
updated: 2026-09-30
---

`image_facts` (crates/cli/src/native/read_loop.rs) proves `_code_fits`,
the image's non-emptiness and its size by evaluating `(spelled).len()`
against literals, for `--read-loop` and `--print`. That walks every byte of
the spelled code, including the encoder's output for every generated piece.
At today's sizes it is within the default fuel. `--fields` passed it with
three copies of the formatter, and since
[[closed-length-facts-evaluate-encodings]] that failure is a refusal in
about a second (`out of fuel reducing a type` at `_code_fits`, and the
kernel refusing `_image`), not a hang.

Shape of a fix: what `--fields` does. A library lemma proves the length
of `read_count_code`/the print code over open parts (`len_append`, as
`read_fields_code_len` does), and the certificate instantiates it with each
generated piece's `_byte_length`. Worth doing when a tail grows, or
whenever the profiles are next touched: the three profiles would then
share one `image_facts` path.

## Log

- 2026-09-30: Landed with the loop-generator fold (06044391, design §3.3): state_code_len states the process code's length over an open loop and tail; --read-loop, --print and --fields all prove their length through it (read_count_code_len and read_fields_code_len), and image_facts has one path, which always takes a length and its proof.
