---
title: Block-scaled formats (P3109 block operations, OCP MX)
status: open
labels: [mathematics,floating-point,design]
area: mathematics
milestone: [ml-float-forward]
created: 2026-11-26
updated: 2026-11-26
---

P3109 §5 defines operations on blocks of values that share a scale factor,
and OCP's MX formats (E4M3/E5M2/E2M1 elements with an E8M0 scale) are the
ML case. Precision one (closed [[float-precision-one]]) makes power-of-two
scale types nearly expressible: an E8M0-like scale is an unsigned
precision-one format without a zero.

Design note first: the scale type (a `Format` with no zero needs a canonical
form that excludes `mag = 0`, or a separate exponent type), a block's value
as scale × elements, and which block operations (dot product, conversion)
to state. Depends on [[float-p3109-operations]].
