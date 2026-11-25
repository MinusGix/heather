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
- 2026-11-25: Second round, after the coordinator's answers: the relative laws, a branch that names its output, and how real sources spell reads.

  **1. Laws relative to the read: the candidate replacement for `StepModelLaws`.** All three asks hold.
  - The definitions:
    - `PathLawsRel(p, fits: V → V → Bool)` takes `fits(read, written)`.
    - `set_get` and `set_set` hold under the fit against the step's read `a`.
    - `reads_fit` gives `fits(a, a)`.
    - `Path::KeepsFitRel(q, fits) = (x, s) → fits(x, s) → (v) → fits(x, q.set(s, v))`.
    - `StepModelRel` and `StepModelLawsRel` follow.
  - (c) **The decider's soundness goes through unchanged.** `Steps::apart_sound_rel` is `Steps::apart_sound`'s proof with `Apart::under_rel` in place of `Apart::under_on`. In `under_on` each `fits(x)` becomes `fits(a, x)` against the outer step's read: `fits(a, a)` comes from `reads_fit`, and the fits of `r.set(a, c)` and `q.set(r.set(a, c), b)` from the relative keeps. Nothing else in the proof touches fits. The denotation is `steps.hthr`'s own (`StepModelRel::steps()`).
  - (b) `StepModelLawsRel::of_laws` lifts any model lawful under `StepModelLaws`, with its fit ignoring the read. `val_model_laws_rel` is `Val`'s, and `val_split_apart_rel` runs `split_at_mut` through the relative soundness.
  - (a) **`Dyn`'s laws come from the structures' laws alone** (`Dyn::model_laws_rel`, given `StrsLaws`: per record, each field's `PathLaws` and the pairwise `Apart` of distinct fields).
    - The model's path dispatches on the owner's code to a native part (`Dyn::part`): `Path::elem` for an element, the library's `Path::window` then a vector-as-list step for a window, and the structure's `Field.path` for a field. Its write decides the written value's code once, outside the part (`Dyn::put_in`).
    - The fit is the read's code, plus the window's length for a window (`Dyn::fits`, `Sel::ok`).
    - The five laws transfer from one part's laws by `Dyn::in_set_get` and its siblings. A fitting write is `Dyn(t, w0)` (`Dyn::fit_at`, through `Dyn::cast_back`, `J` with the code free), and the write at its own code is the part's write (`Dyn::put_in_at`, through `Shape::dec_self`).
    - Keeps: a write keeps the owner's code definitionally (the write is `Dyn(d.code, …)`) and a sequence's length (`PathIn.shape`).
    - Apartness: the parts' spans (`PathIn::apart_sound`) or the structure's field apartness.
    - **Beyond the dictionaries' laws, nothing was needed. No UIP anywhere**: every cast is at a decision known to be `refl` by `dec_self`, or under `J` with an endpoint free.
  - `Point`'s instance is written by hand in the probes (`Point::fields_laws`, `pt_strs_laws`). `xy_apart` finds `ps[i].x` and `ps[i].y` apart owing nothing; `elems_x_apart` finds `ps[i].x` and `ps[l].x` apart owing `i ≠ l`, discharged from the source's `ne`.
  - The model's write is not the meaning's `Dyn::over`. They agree where the write fits; relating them is item 8's step lemma, still not built.

  **2. A branch that names its output** (`Join(cd, a, wa, b, wb, rest)`). Each arm runs from the branch's state and its bindings end with it. The output is `convoy(test, wa at a's end, wb at b's end)` (`Sem::joined`, each arm's state an argument so it is evaluated once), and `rest` runs once. `mean_then` takes its result type `R` as a value argument, because the arms' states are a call at `R = Sem` and polymorphic recursion is not lowered. The arms here bind words only; the objects pass through.
  - **A function that continues after its `if` pins by `refl`.** `after_join` is `let a = if h: i < ps.len() { ps[i].x } else { 0 }; ps[a].y`. It pins both through the word (`after_join_reflects`) and through the whole output record (`after_join_whole`), since no convoy over the record is left. The control is refused (`after_join_not_x`).
  - Its residuals: the arm's bound is `Bool::cases` of the `if`'s evidence, and the read after the join owes its bound at the joined word, which the source states as written (`after_join_site`).
  - Cost: N joins each testing the parameter, each arm's bound discharged, as one restated conjunction (`j_both`): 41.7k, 78.9k, 153k and 302k steps at 64 to 512. That is linear, about 1.9 times a plain read per join.
  - A chain where each join's test and arm read the previous joined word is **quadratic** (3.3k, 8.7k, 17.9k, 32.2k, 52.8k and 81.1k steps at N = 2 to 12) and runs out of fuel by N = 64. The joined value is substituted into both the next test and the next arm and re-evaluated at each use: a computed value is shared only by closure identity (`docs/proof-patterns.md` §1). The source's `let` chain has the same term. That is an elaboration-sharing cost, not a join cost.

  **3. Total reads and the inhabitant, on real sources** (no machinery built).
  - (a) **Today's `runtime fn` sources spell an element read as a proof-carrying call whose body is total with a default.** `Vec::at(v, i, inside: ∥i.toNat() < n∥ := bv_omega)` is `vector_get(v, i.toNat(), BitVec::ofNat(0))`, and `Bytes::at` is `byte_within`, 0 past the length. The squashed bound is an erased parameter the body never reads, as the fifth experiment's `pick` was. A write is `Vec::put` (`vector_update`), total, with its bound likewise unused. The arena (`a.heap.at(base + i)`), the word map (`m.keys.at(j)` under `if lt: j < 4`) and the linked lexer (`Bytes::at`) all spell it this way. `Vec::at` exists only at words, where 0 is the inhabitant.
  - (b) The spelling with an unused proof pins by `refl` against the total read (`read_w_reflects`, `List::at_word` in `Vec::at`'s shape). A read that consumes its proof is refused by `refl` (`get_x_below_refl`, `List::at_below` by recursion on the proof; `vector_index` at the proof, which `Vec::at_index` relates `Vec::at` to, is the library's instance). It holds by one library lemma per site: `List::at_below_total`, the read under its bound is the total read at any inhabitant (`get_x_below_pin`).
  - (c) **The inhabitant can live only in the pin's statement, quantified, and the function then takes no `T`.** A write that reads nothing at `T` pins by `refl` at every inhabitant (`put_elem_reflects`, `∀ d`). A read at `T` cannot be `refl`: the meaning's read is `unwrap_or(d)`, and a source with no `d` cannot spell it. It must use the proof-consuming read plus the lemma of (b) (`copy_below_pin`, `∀ d`). So for an open `T` the choice is the `Default` bound or one lemma per read.

  **The measurements were re-run** after `mean_then`'s change and are within noise of the first round: `c_both` 21.8k, 41.8k, 81.7k, 162k; `u_both` 13.8k, 26.4k, 51.7k, 102k.
