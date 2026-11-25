---
title: Ownership: the universal value as a native value tagged with its code (sixth experiment)
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The sixth ownership experiment (docs/language/ownership-design.md §18.4 item 4). Five experiments built the checker so that its soundness theorem is stated once, over a reflected body and a meaning function. Their headline results were two: a source function pins to its reflected body's meaning by `refl`, and a residual is discharged by the source's own proof by conversion. Both were shown only where every object is a `List<Nat>`. A real function has records, lists of records and type parameters, and the library's universal value (`Val`, `value_steps.hthr`) would make the meaning compute on an encoding.

The proposal under test: **the universal value is a native value tagged with its code.**
- `Shape` is a closed, first-order code: a word, a sequence, or a named type.
- `El(tys, c)` decodes it by large elimination.
- A second environment gives each named type its structure: opaque, or a record's field paths.
- `Dyn(tys)` is a code with a value of its decoding, used as the single sort of `StepModel`.

## Scope

New files only: `lib/lang/ownership/coded.hthr` and `lib/_tests/lang/ownership/coded_tests.hthr`.
1. Codes, the decoding, the environments, `Dyn`, a cast that computes, and `decide_self` without UIP.
2. The step model at `Dyn` with its `StepModelLaws`.
3. A fixture meaning.
4. Pins: a field of an element of a list of records, a write of one, a generic function at an open `T`, an `if h:` guarding a read, and calls passing a record and a window.
5. Residuals as the source writes them.
6. The control through `Val`.
7. Cost at doubling sizes against uncoded bodies.

Refuted by any of these: a pin over a record that is not a conversion; a cast that does not reduce on closed codes; UIP needed; a universe restriction; non-linear cost or a large factor.

## What it assumes from elsewhere

- **[[ownership-site-facts-into-the-checker]]** owns the checker whose pins, residuals and restated conjunction this mirrors in a fixture.
- **[[reflected-languages-typed-by-construction]]** (closed) measured code-indexed syntax; this keeps the syntax untyped and types only the values.
- **[[uip-from-decidable-equality]]** was expected to be needed and was not.

## Done when

Items 1 to 7 are answered with probes in `lib/_tests`, the log reports what pins by `refl` and the measured shapes, and `ownership-design.md` §18.4 has the result as its item 4.

## Log

- 2026-11-25: Built on branch `claude/ownership-coded-values`: `lib/lang/ownership/coded.hthr`, probes in `lib/_tests/lang/ownership/coded_tests.hthr`.

  **The answer in one line**: the pins and the discharges survive codes. Every pin asked for is a conversion over a list of user records and at an open type parameter, and every residual is the source's own proof by conversion, at linear cost and about 1.5 to 2.3 times the uncoded steps. What does not survive is `steps.hthr`'s `StepModelLaws` at `Dyn`: as stated, no fit makes a typed step lawful (a theorem, below). The coordinator was told when that was found and the variant was not built.

  **1. Codes.**
  - `Shape { SWord, SSeq(a), SNamed(k) }`; the type environment `tys: Nat → Type`; `El(tys, c)` by large elimination (`El(tys, SNamed(k)) = tys(k)`).
  - The structures, after `tys`: `Strs(tys) = (k: Nat) → Struct(tys, tys(k))`, where `Struct` is `Opaque(d)` or `Fields(d, fs)` and each `Field` holds a shape and a `Path<T, El(tys, shape)>`.
  - `Dyn(tys) = { code: Shape, val: El(tys, code) }`.
  - No universe or large-elimination refusal. `Pres` is `Type<1>`, as expected. A `List<Type>` environment works too, but its literal is refused (`List<Type<1>>` has no `CollectionLiteral`, and universes are non-cumulative), while the manual-`Cons` lint still asks for one. `Nat → Type` avoids both.
  - The decision `Shape::dec`, the cast `Shape::cast` (`j` along the proof) and `Dyn::back` are `fn`s whose `Inl` proof is built from `refl` by `fn` congruences (`cong_seq`, `cong_named`, `Nat::cong_succ`). At two closed equal codes the decision is `Inl(refl)` by evaluation and the cast is the identity (`dec_closed`, `back_closed`).
  - `Shape::dec_self(c): dec(c, c) = Inl(refl)` is proved by induction on the code, with `Nat::dec_self` under it. **No unique identity proofs were needed anywhere**: every cast in a law or pin is at a decision whose result is known to be `refl`, never at an arbitrary `p: c = c`. [[uip-from-decidable-equality]] is not a prerequisite of this design.

  **2. The step model: refuted as stated.**
  - `Dyn::path(sel)` instantiates `StepModel<Dyn>`: the part with its code where the step fits the owner's code, and `None` otherwise.
  - Its laws cannot hold: `Dyn::elem_not_lawful(fits): ¬PathLawsOn(Dyn::path(…, OnSeq(SeqOne(0))), fits)` for every `fits`, and `Dyn::model_not_lawful` lifts it to `¬StepModelLaws`. The reason is that `fits: Sel → S → Bool` sees only the written value, while `reads_fit` makes every value read through a step fit. One selection reads a word from a `List<Nat>` and a list from a `List<List<Nat>>`, so both codes fit, and `set_get` then demands that a list written into a `List<Nat>` reads back. `Val` satisfies the laws only because its sequences are heterogeneous.
  - The fix I would make (proposed, not built): make the fit relative to what the step replaces, `fits: Sel → S → S → Bool` (read, written), with `set_get` and `set_set` under it. `Val`'s window fit (`fits_seq(n)`) is then "the length of what was read", and `Dyn`'s is "the code of what was read". `KeepsFit` becomes "a write keeps the owner's code", which every `Dyn` write does by construction, because a write of another code writes nothing.

  **3. The meaning (a fixture).**
  - Places are an object and steps. `Get`, `Put` (a word, or the value at another place), `Add`, `Call` of a native callee through a world of callee meanings (`World(tys) = Nat → List<Dyn> → List<Nat> → Nat`), and a branch that is the convoy of `if h: i < p.len()`.
  - **What makes it convert: the meaning reads totally and writes by modifying, never through the paths' `Option`.** `Dyn::at` reads an absent element as the code's inhabitant (`Dyn::dflt`: 0, `Nil`, or the named type's own). `Dyn::over` hands the part to a function and puts back its result where the code matches. So the code of everything produced is a function of codes alone, every dispatch along a place of closed codes reduces, and what remains is the native operation on the value.
  - Through `Path.get`, the composition `p.get(s).and_then(q.get)` and the write `then_set`'s `match p.get(s)` stop at the stuck `ps.nth(i)`. That would be a case-of-case the kernel does not do.
  - The price is an inhabitant per named type: a `Default` in the derived instance, and for a type parameter a `T` given to the function.

  **4. Pins.** Each one is by `refl`, with a refused control where one makes sense.
  - `ps[i].x`: `get_x_pin` through `Dyn::read`, and `get_x_reflects` through the meaning. Source `ps.nth(i).unwrap_or(Point::origin()).x`. The control (`.y`) is refused.
  - `ps[i].x := v`: `set_x_reflects` against `ps.update(i, λ p => Point(v, p.y))`, the explicit functional update. The surface parses `ps[i].x := v` but desugars it to `ps.put(i, …)` and a proof-carrying `at`, which `List` lacks; a meaning without proofs could not spell `at`'s found proof anyway. The control is refused.
  - A generic function at an open `T`, with the environment `[T]` and `T` opaque with the given inhabitant `d`. `xs[i] := xs[j]` is `copy_elem_reflects`, against `xs.update(i, λ _ => xs.nth(j).unwrap_or(d))`, and its answer `xs[i]` is `copy_elem_answers`.
  - `if h: i < ps.len()` guarding a read: `guarded_reflects`. It pins with the answer read inside the continuation (`mean_word`). `.word` of the whole output record does not pin (`guarded_projected`, refused): the projection meets a convoy over the record. This is not about codes; it is [[ownership-pin-after-join]]'s cousin, and a meaning answering through its continuation removes it.
  - Calls: `call_gap_reflects` passes `ps[i]` to `gap(p, ok: p.y <= p.x)`, and `call_total_reflects` passes the window `ps.drop(lo).take(n)` to `total`. The world's entry takes its argument by `Dyn::as_code`, which is the native value at a closed code.

  **5. Residuals.** The bound `∥i < ps.len()∥` over the list inside the `Dyn` (`get_x_site`), the branch's bound from `decide_true(e)` (`guarded_site`), `gap`'s precondition at the record passed (`call_gap_site`), and `total`'s at the window passed (`call_total_site`). Each is the source's own term, by conversion; none needed a lemma.

  **6. The control through `Val`.** `get_x_val_pin`, the same read over `VSeq(Vals::of(ps.map(enc_pt)))`, is refused by `refl`. It holds by `get_x_val`, an induction on the list, and that is the cost per operation and per encoding (a write, a window and each record shape would each need their own), again for every residual stated over the encoding.

  **7. Cost** in kernel steps. Release build, width one, a fresh copy of a warm store per run, read with `scripts/timings`. The harness was generated in a scratch directory and not committed. Bodies of N reads, each owing its bound; "both" is the pin and the discharge as one restated conjunction (`⟨refl, rep(N, inside)⟩` ascribed once); "chain" is word k+1 read at word k, pinned by `refl` against a recursive source.

  | N | coded, `ps[i].x` both | coded, `xs[i]` both | uncoded both | coded `ps[i].x` chain | coded `xs[i]` chain | uncoded chain |
  |---|---|---|---|---|---|---|
  | 64 | 21.8k | 21.1k | 13.8k | 43.7k | 33.2k | 19.4k |
  | 128 | 41.7k | 40.5k | 26.4k | 87.0k | 65.9k | 38.3k |
  | 256 | 81.5k | 79.2k | 51.7k | 174k | 131k | 76.2k |
  | 512 | 161k | 157k | 102k | 347k | 262k | 152k |

  - Every column is linear: each doubling doubles the steps.
  - The factor over the uncoded meaning at the same reads is 1.5 (both) and 1.7 (chain); the field of a record element adds 1.0 and 1.3 more. That makes 1.6 and 2.3 for `ps[i].x` against `xs[i]`.
  - At 512 the slowest item took 0.15 s.
  - The uncoded twin is in line with the checker branch's own measurements (its let-chain pin was 154k at 512, this one 152k), so the factor is against a fair baseline. Part of it is the fixture's generality (places, `obj_at`, the object list), not the codes.

  **8. Not built.** It asks for one step lemma "from `StepModelLaws` alone", and item 2 refutes those laws at `Dyn` as stated. With the relative fit of item 2 it is the next thing to try.
