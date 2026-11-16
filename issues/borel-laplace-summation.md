---
title: Borel–Laplace summation as a differential-algebra homomorphism
status: open
labels: [mathematics,analysis]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

`docs/library/analysis-foundations-design.md` §3.8: Borel–Laplace summation of
Gevrey-1 series. It is a homomorphism of differential algebras on its domain,
so formal identities and ODEs transfer to the summed functions.

Scope:

- Gevrey classes as a growth law on certified-expansion constants
  (`C_N ≈ A·Bᴺ·N!`);
- the Borel transform (coefficients divided by `n!`, giving a convergent
  series), its analytic continuation along a ray, and the Laplace integral
  with an explicit tail bound;
- the homomorphism: `+`, `·` (convolution on the Borel side), `d`, and
  composition where it holds;
- Watson's uniqueness theorem in a sector of opening greater than `π`;
- Euler's series as the probe, identified with [[stieltjes-pade-enclosures]]'
  value;
- optimal truncation with its exponentially small error, stated for the
  transseries side.

Multisummation, resurgence and the Stokes phenomenon belong to
[[grid-based-transseries]].

## What it assumes from elsewhere
- **[[summation-methods]]**: the interface.
- **[[certified-expansions]]**: the asymptotic reading.
- **[[power-series-evaluation]]**: convergent evaluation for the Borel transform.
- **[[real-functions-and-derivatives]]**: integration, if it lands there.
  Otherwise this issue needs the Bishop integral of design note §12.
