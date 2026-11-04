# Bool guards read through `Reflects`

`Format::canonical_intro` and `Format::canonical_elim`
(`lib/std/num/float/float.hthr`) were the prompt: two short facts that took
45 lines between them. This note says why, what landed (2026-10-30), and what
would make the rest of the pattern disappear.

## 1. The shape of the problem

`Finite(F)` carries its canonical form as a Bool guard, so the proof field is
proof-irrelevant and closed formats decide it by `refl`:

```heather
fn Format::canonical(self F: Format, mag, bexp: Nat) → Bool {
    let normal = match bexp { Zero => True, Succ(_) => F.half().leb(mag) };
    let reserved = F.specials.reserves_top() && F.span.leb(bexp) && F.top().leb(Succ(mag));
    Succ(mag).leb(F.top()) && bexp.leb(F.span) && normal && !reserved
}
```

Every client wants the four conditions as facts about naturals. Getting from
one to the other was done by hand, one `&&` at a time, in both directions:

```heather
// before: canonical_intro (the elim was the mirror image, 20 lines)
let fits_bit = Succ(mag).leb_complete(F.top(), fits);
let range_bit = bexp.leb_complete(F.span, range);
let normal_bit = match bexp as λ b => (b = 0 ∨ F.half() <= mag) → (match b { … }).IsTrue() { … }(normal);
let reserved = F.specials.reserves_top() && F.span.leb(bexp) && F.top().leb(Succ(mag));
let free_bit = reserved.is_true_not_intro(λ r => {
    let rs = (F.specials.reserves_top() && F.span.leb(bexp)).is_true_and(F.top().leb(Succ(mag)), r);
    let rr = F.specials.reserves_top().is_true_and(F.span.leb(bexp), rs.left);
    …
});
(Succ(mag).leb(F.top()) && bexp.leb(F.span) && (match bexp { … })).is_true_and_intro(!reserved,
    (Succ(mag).leb(F.top()) && bexp.leb(F.span)).is_true_and_intro(match bexp { … },
        Succ(mag).leb(F.top()).is_true_and_intro(bexp.leb(F.span), fits_bit, range_bit), normal_bit),
    free_bit)
```

Three things make it long:

1. **The Bool API is per-connective and one-directional.** `is_true_and`,
   `is_true_and_intro`, `is_true_not`, `is_true_not_intro`, `leb_sound`,
   `leb_complete` each take one step, and each takes the *other operand
   spelled out* (`a.is_true_and(b, h)`), so every step restates a prefix of
   the guard. Intro and elim are written twice, mirrored.
2. **The library already had the right object but not at `IsTrue`.**
   `Reflects(P, bit)` and `reflects_and/or/not` existed for `Decide`, stated
   at `bit = True`; nothing consumed a `Reflects` at `b.IsTrue()`, nothing
   built one from a `sound`/`complete` pair (`nat`'s TODO above `leb_sound`
   asked for exactly that), `Nat::leb` had no `Reflects`, and `reflects_iff`
   lived privately in `float/literal`.
3. **No automation reads a Bool guard.** `omega` reads relations and splits
   `∧`/`∨` facts (§13 of `docs/omega-measure-reduction-design.md`), but a
   `b.IsTrue()` fact is skipped whatever `b` is.

The pattern is not float's: 24 library files take guards apart with
`is_true_and`/`leb_sound`/`leb_complete` (x86 asm tables 40 uses, FunctionIR
eval 38, structured meaning 26, …).

## 2. What landed: one reflection, read both ways

`bool` now has the `IsTrue`-side vocabulary, and the connective lemmas take
their propositions and bits as implicits:

| lemma | says |
|---|---|
| `reflects_of_is_true(sound, complete)` | a sound/complete pair is a `Reflects` |
| `reflects_and(p, q)`, `reflects_or`, `reflects_not` | the connectives (now implicit `P, Q, x, y`) |
| `reflects_iff(r, pq, qp)` | move a reflection along an equivalence (was private to `literal`) |
| `reflects_intro(r, p): b.IsTrue()` | prove the guard from the proposition |
| `reflects_elim(r, h): P` | read the proposition out of the guard |
| `Bool::is_true_reflects(b)` | a Bool atom reflects itself |
| `Nat::leb_reflects(n, m)` | `leb` reflects `<=` |

float states the proposition once, proves the reflection once, and the two
theorems become one line each:

```heather
fn Format::Canonical(self F: Format, mag, bexp: Nat) → Type {
    Succ(mag) <= F.top() ∧ bexp <= F.span ∧ (bexp = 0 ∨ F.half() <= mag)
        ∧ (F.specials.reserves_top().IsTrue() → F.span <= bexp → Succ(Succ(mag)) <= F.top())
}

theorem Format::canonical_reflects(self F: Format, mag, bexp: Nat): Reflects(F.Canonical(mag, bexp), F.canonical(mag, bexp)) {
    let normal = match bexp as λ b => Reflects(b = 0 ∨ F.half() <= mag, match b { Zero => True, Succ(_) => F.half().leb(mag) }) {
        Zero => reflects_of_is_true(λ _ => Inl(refl), λ _ => trivial),
        Succ(_) => reflects_iff(F.half().leb_reflects(mag), λ le => Inr(le), λ n => match n { Inl(zero) => false_elim(omega(zero)), Inr(le) => le }),
    };
    let reserved = reflects_and(reflects_and(F.specials.reserves_top().is_true_reflects(), F.span.leb_reflects(bexp)), F.top().leb_reflects(Succ(mag)));
    let tests = reflects_and(reflects_and(Succ(mag).leb_reflects(F.top()), bexp.leb_reflects(F.span)), normal);
    reflects_iff(reflects_and(tests, reflects_not(reserved)),
        λ c => And(c.left.left.left, And(c.left.left.right, And(c.left.right, λ rt sp => {
            let over: ¬(F.top() <= Succ(mag)) = λ o => c.right(And(And(rt, sp), o));
            omega
        }))),
        λ c => And(And(And(c.left, c.right.left), c.right.right.left), λ r => {
            let room = c.right.right.right(r.left.left, r.left.right);
            omega
        }))
}

theorem Format::canonical_intro(…): F.canonical(mag, bexp).IsTrue() {
    reflects_intro(F.canonical_reflects(mag, bexp), And(fits, And(range, And(normal, free))))
}

theorem Format::canonical_elim(…): … { reflects_elim(F.canonical_reflects(mag, bexp), ok) }
```

The reflection is built *in the guard's own shape* (left-nested `&&`, the
`!reserved`), so it checks by conversion with no restatement; the only real
reasoning left is the `reflects_iff` at the end, which turns
`¬(rt ∧ sp ∧ top <= mag + 1)` into the implication the statement wants, and
that is two `omega`s. The theorems' signatures are unchanged, so no caller
moved.

## 3. What would remove the rest

Two larger steps, filed as issues; each deletes a different part of §2.

### 3.1 Comparison decisions whose bit is `leb` ([[decide-bit-is-the-comparison]])

> **Landed 2026-10-30.** As below, except that `canonical` spells its
> proposition inside `decide_bit<…>()` rather than naming `F.Canonical`:
> instance search does not unfold a defined proposition
> ([[decide-at-defined-proposition]]), so `Canonical` was folded into
> `canonical`'s body and intro/elim are `decide_intro(…)` / `decide_elim(ok)`.
> The issue's resolution records what else moved.

`Decide<n <= m>`'s bit is `or_bit(Nat::le_dec(n, m))`, not `n.leb(m)`, so a
`decide_bit<P>()` over `<=` is never the guard a program writes. With the bit
`leb` (reflection `Nat::leb_reflects`) and a `Decide<P → Q>` instance (bit
`!x || y`), the guard *is* a decision of the proposition, and the whole of §2
collapses to the class:

```heather
fn Format::canonical(self F: Format, mag, bexp: Nat) → Bool { decide_bit<F.Canonical(mag, bexp)>() }
theorem Format::canonical_intro(…) { decide_intro<F.Canonical(mag, bexp)>(And(fits, And(range, And(normal, free)))) }
theorem Format::canonical_elim(…) { decide_elim<F.Canonical(mag, bexp)>(ok) }
```

`canonical_reflects` disappears (it is `F.Canonical(mag, bexp).reflects`),
and the hand-built bits in `float/literal`'s `dy_exact` go the same way. The
cost is a definition change: `canonical`'s least-exponent test becomes
`bexp = 0 ∨ …`'s bit rather than a `match bexp`, and every closed `refl` over
`canonical` (`float_tests`, `arith_tests`) re-evaluates through the
dictionaries; the issue owns measuring that and the native frontend's reading
of `if n <= m`.

### 3.2 omega reads Bool guards ([[omega-reads-bool-guards]])

Landed 2026-10-30 (§17 of `docs/omega-measure-reduction-design.md`):
`canonical_elim` is now the `omega(ok)` form below, the atom
`reserves_top()` is the Nat atom `omega::bit(r)`, and the stuck `match` in
`normal` is [[omega-guard-reads-nat-match]]. The sketch as filed:

The general fix for the 24 files. `omega` reading a fact `b.IsTrue()` by the
guard's structure (`leb` as `<=`, `&&` as `∧`, `||` as `∨`, `!` as
`¬`, δ through a Bool definition such as `canonical`, a stuck
`match n { Zero => …, Succ(_) => … }` split by cases), with `Nat::leb_reflects`
and the `Bool::is_true_*` lemmas as the reconstruction, would let a client whose
elim only feeds omega skip it:

```heather
// today
let c = F.canonical_elim(g.mag, g.bexp, g.ok);
… omega        // reads c.left, c.right.left, … as split conjuncts
// with 3.2
… omega(g.ok)  // reads the guard itself
```

(callers that pass a conjunct to a lemma, such as `units_le_max`'s
`Nat::mul_le_mono_r(…, c.left)`, keep the elim), and makes `canonical_elim` itself
`And(omega(ok), And(omega(ok), And(omega(ok), λ rt sp => omega(ok, rt, sp))))`
(omega closing an `∨` goal is a further step; the disjunct stays a
`reflects_elim`). The Bool atom `reserves_top()` is the part that is new to
omega: it is propositional, not arithmetic, so it needs an atom that is
neither `Nat` nor `Int`; the issue owns that choice.
