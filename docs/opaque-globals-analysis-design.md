# Opaque globals for analysis: the pull API's body half, and callee markers

> **Partly burned in B2 (2026-10-24).** The pull API's body half (`fn_body_code`, the marked
> boxed body) had certgen as its only consumer and was deleted with it
> (`docs/native-program-logic-design.md` §3.2); `fn_type_code` stays. The last commit with
> the body half is `82521eab`.

Design for `issues/opaque-globals-analysis.md` — blocker (1) of the
2026-08-02 expressiveness verdict, scheduled as its own round: let
in-language code analysis see through global references (`u^δ`), behind the
pull reflection API the fn-reflection round pre-cut. Round pattern as usual:
this document first, the implementation against §8's acceptance list.

Context it builds on and does not restate: the transcriber round
(`docs/archive/certgen-transcriber-in-language-design.md` — the marker convention,
the analyzer-slot harness, `lib/certgen/certgen_code.hthr`), the signature-reflection
round (`docs/fn-signature-reflection-design.md` — `Elaborator::fn_type_code`,
the interface/implementation seam this round was expected to fill from the
kernel side), and the definitions round
(`issues/simulate-conversion-cost.md`, 2026-07-31 closing entries —
layer-indexed transparency: δ fires at p/m, layer c is opaque, bodies live in
`GlobalBinding::Tm`).

## 1. The route fork, settled against the book

The charter names two routes and invites a third:

- **(A) a recursor branch for global references** — `elim^Trm` (and
  `elim^Typ`) gain a `tm_global`/`ty_global` branch, so `box (u^δ)` fires
  instead of going neutral;
- **(B) unfolding-for-analysis** — `u^δ` unfolds to its definition body at
  the point where an analyzer or reflection primitive requests it;
- **(C) elaborator-side shapes** — an unfold before boxing, or an explicit
  unfold primitive at layer m.

**Decision: (B), implemented entirely at the reflection boundary — a pull
primitive plus an extension of the marker convention. No kernel change of any
kind.** The kernel's branch table, neutrality laws, conversion rules, and
layer-indexed transparency are untouched, verbatim. The argument, from the
book:

**(A) is a shared-notion edit, and the book says the blocking is deliberate.**
Ch. 06's neutral-form grammar (ll. 24–37) includes
`elim^Typ … (box U^δ)` and `elim^Trm … (box u^δ)` as neutral *productions*,
with the explicit remark "for the recursive principles, we block on global
variables, following \citet{hu2024layered}" — a cited design decision. Two
dedicated convertibility rules (ll. 640–661) compare such neutrals with the
globals compared *syntactically*, and ch. 07's logical relations carry the
matching cases (`07_logical_relations_for.tex` ll. 385, 396). A branch for
globals deletes two neutral productions, two conversion rules, and two
relation cases — a ch. 06 **and** ch. 07 edit, which is exactly the
stop-and-ask condition the Coq-formalization discipline names. The kernel
agrees everywhere the book does: `reduce.rs::is_neutral_term` (~2181, the
`ElimCodeTy`/`ElimCodeTm` box-of-global arms), `Defs::opaque`'s module doc
("exactly as in ch. 06's reduction relation"), and the definitions round's
own tests pin `elim^Trm` neutral on `box (u^δ)` *and* told apart by which
global it carries.

**(A) would not even serve the customers.** The branch's telescope could only
follow `tm_var`'s pattern: a fresh Ψ-global `u_g : Trm_{i'}(Δ ⊢ T)`
abstracting over the reference, one branch body for every global at once. The
analyzer could re-box it but never observe *which* global it holds — the same
load-bearing opacity `issues/code-variable-analysis-api.md` records for
variables (a recursor that distinguished them would break elimination's
commuting with global substitution; ch. 07b's `u`-cases are exactly the
stability the branch would have to preserve). Cross-function transcription
needs the callee's *identity* (a `LetCall` names its callee); a branch
delivers a hole where the identity goes. Making it deliver more — an index
into Ψ as data — is an intensional-analysis extension strictly bigger than
the neutrality edit, with no book support at all.

**Kernel-side unfolding at layer c breaks the design fact everything leans
on.** "Code does not compute" (conversion on code is structural, boxed code
compares with `==`) is what makes ElabCode-style round-trip pins `refl` and
what made the definitions round's layer-indexed transparency sound — ch. 06
compares boxed globals syntactically, so δ *must not* fire at c
(`issues/simulate-conversion-cost.md`, 2026-07-31: "transparency must be
layer-indexed (unfold at p, neutral at c)"). An unfold rule at c would make
`box (u^δ)` convertible with `box (body)`, which the definitions round pins
as *not* convertible. Same stop condition, worse consequences.

**An explicit unfold primitive at layer m** (`unfold : Code(Δ ⊢ T) → Code(Δ ⊢ T)`,
a new term former reducing `box (u^δ)` to `box (body)`) is priced for
completeness: a new ch. 04 former with typing, reduction and congruence
rules, its own ch. 06 neutral form (stuck on a *bodyless* global), and a
ch. 07 case — a smaller edit than (A) but still a shared-notion round, and
its one advantage over the pull primitive (usable mid-walk, inside a branch)
is exactly what no current customer needs: the walk receives whole bodies
from the harness, not code values it discovers mid-flight. Deferred with its
first real customer (§7).

**What (B)-as-a-pull-primitive means, honestly.** Globals stay opaque
*inside* code, everywhere, forever — that is the fence the theory wants. The
place opacity is lifted is the reflection API, per name, on request, by the
elaborator — the one party that owns Ψ and is already trusted to *build* the
code being analyzed (it elaborated it). "u^δ unfolds to its definition body
at the point where a reflection primitive requests it" is precisely
`fn_body_code(name)`: ask for `add`, receive `add`'s body as code. And the
analyzer-visible identity of a callee *inside* another body is delivered the
same way variable identity was: by the marker convention, extended (§3).
Nothing moves the trust boundary — markers are an untrusted elaborator
transformation, the walker is an untrusted library, and everything either
emits is kernel-checked downstream, exactly as before.

## 2. The body-reflection primitive, named and cut

The fn-reflection round left the body primitive "to be named with the
opaque-globals round". Named:

```rust
pub struct BodyCode {
    pub arity: usize,        // parameters peeled off the Lam spine
    pub callees: Vec<String>, // callee-marker table: tag i+1 = callees[i]
    pub code: Term,          // BoxTm(marked body) : Code(· ⊢ Nat)
}
impl Elaborator {
    pub fn fn_body_code(&self, name: &str) -> Result<BodyCode, String>;
}
```

- **Pull, per invocation, nothing stored.** The body is read out of Ψ
  (`GlobalBinding::Tm`'s `body`, the definitions round's field) on request —
  the same stance as `fn_type_code`, and the same honesty about staging: when
  the elaborator is Heather, this is an ordinary metaprogram operation.
- **The stance on markers: marked code IS the reflection contract.** The
  primitive returns the body with every bound-variable occurrence replaced by
  a level marker (the transcriber round's convention, unchanged) **and every
  cross-function call head replaced by a callee marker** (§3), plus the table
  mapping marker tags back to names. Raw bodies — de Bruijn variables, live
  `u^δ` nodes — are *not* an interface this round exposes: a raw variable is
  unanalyzable (tm_var's opacity) and a raw global is neutral, so a raw body
  is precisely the thing an analyzer cannot use. The primitive hands over the
  analyzable coordinate system and the key to read it.
- **A body-less global declines.** Theorems are deliberately body-less
  (proofs opaque; `global_body` returns `None`), so
  `fn_body_code(theorem)` is `Err("… has no elaborated body to analyse")` —
  a decline, pinned by test, never a panic and never an empty box.
- **Fragment residue stays where it was.** The primitive still peels the Lam
  spine via `sig_peel` (marking needs the body under its binders at a known
  depth) — the agreement-oracle role from the signature-reflection round is
  unchanged.
- **The contract's DOMAIN is the certgen fragment, and widens per-fragment**
  (coordinator review, 2026-08-11). The name reads as the general
  body-reflection primitive; the contract is not general yet:
  `MarkCx::callee` enforces `Nat`-chain signatures, `mark` enforces the
  fragment's term grammar, and both marker shapes are typed at `Nat`. A
  general version — the ElabCode reflect direction's appetite — needs
  markers at arbitrary types, and **each widening reopens the recognizer's
  unambiguity argument** (§3's "fragment source contains no λ" is a
  per-fragment fact, re-established or replaced whenever the domain grows).
  The *interface* is general; the domain is not, and saying so here is what
  keeps the next fragment round from discovering it as a surprise.

**`fn_type_code`'s implementation swap is a no-op, recorded as a
correction.** The signature-reflection round wrote (doc §1, and the
`fn_type_code` doc comment) that this round "replaces that *body* with `u^δ`
unfolding-for-analysis under its ch. 07 obligations". With route (B) settled
at the reflection boundary there is no kernel machinery to swap in: the
Ψ-read + `shift_global` implementation *already is* unfolding-on-request,
and it is final, with no ch. 07 obligations because the kernel never learns
about it. The placeholder paragraph comes out of the comment; the interface
was right and the anticipated implementation change was not needed.

## 3. Callee markers: the marker convention's second clause

The transcriber's convention 1: a bound-variable occurrence arrives as
`(λ (x : Nat). x) ⌜level⌝`. This round adds:

**Convention 3 (callee markers).** A cross-function call head — a `u^δ`
reference to a fn of fragment type `Nat → … → Nat` with arity `k ≥ 1` — is
replaced before boxing by the closed term

    callee_marker(c, k)  :=  λ (x₁ : Nat). … λ (x_k : Nat). ⌜c⌝

with tags `c = 1, 2, …` minted in first-occurrence order and the table
`tag → name` returned beside the code (`BodyCode::callees`; tag `c` is
`callees[c-1]`). The call's argument spine is left in place and marked
recursively, so `add(a, mul(a, k))` becomes
`App(App(callee_marker(1,2), var-marker(0)), ih-marker)`.

Why this shape:

- **Type-correct and closed.** The marker has exactly the head's type, so the
  marked body still checks at layer c in the empty context; nothing about
  boxing changes.
- **Stable syntax.** Code does not compute, so the λ-chain never β-reduces
  against its arguments; `beta_elim_tm` dispatches the applications to
  `tm_app` and the chain to `tm_lam`, and the walker reads the tag out of the
  chain's numeral body.
- **Unambiguous within the fragment, heuristically — the standing stance.**
  Fragment source contains no λ at all (bodies are β-normal; eliminator arms
  are binder syntax, not lambdas), so every λ the walker meets is half of a
  marker: body a variable leaf → the identity, i.e. a variable marker's head;
  body a numeral (possibly under more λs) → a callee marker. The two clauses
  cannot collide (`λx.x` vs `λx.⌜c⌝` differ in the body). As with convention
  1, this is a *recognizer*, not a proof — a misread is a refused certificate,
  and the forgeability watch of `issues/code-variable-analysis-api.md`
  (the day the fragment grows genuine App/Lam) covers this clause the same
  as the first.
- **Nullary callees are refused at marking** (`k = 0` would make the marker a
  bare numeral — ambiguous with literals). No loss: nullary fns are outside
  the fragment by the signature rule anyway.
- **A body-less callee is refused at marking**, with the message naming the
  policy (a call to a theorem/declaration is not fragment code). Same
  fail-safe shape as every other decline.
- **Resolution is the Defs convention run backwards.** In a stored body
  (prefix-scoped to the Ψ of length `abs` at its binding), `GlobalVar(v)`
  names binding `abs - 1 - v` — the same arithmetic `Defs::body`'s
  `shift_global(v + 1)` embodies, used here to find the callee's name and
  type (arity check: `Nat → … → Nat`).

**Global references in *types* (`U^δ`) are out of scope, by policy, not
accident**: the fragment's types are `Nat`-chains and contain no `U^δ`; a
type that does contain one walks into `check_sig`'s default arm and
declines. Nothing new to build, one sentence to state.

## 4. The walker: calls as data, and the in-language numbering

`lib/certgen/certgen_code.hthr` gains (all additive — no existing constructor,
helper, shell or slot signature changes):

- `Pre` gains `PCall(c: Nat, args: PRefs, rest: Pre)` — a saturated foreign
  call, rendered as `LetCall(c, …)`.
- `TA` gains `TFn(c, rem)` (a callee-marker chain: `rem` λs around `⌜c⌝`)
  and `TPart(c, rem, pre, len, args)` (a partially applied call: arguments
  compiled so far as a merged prefix + collected refs).
- Prefix composition helpers, the first time two compiled sub-expressions
  meet: `shift_ref`/`shift_refs`/`shift_pre` (re-base `RLoc` indices by an
  offset), `pre_append`, `qsnoc`, `ta_val` (a value as
  `(prefix, ref, len)` — a numeral becomes its `num_pre`).
- `ta_lam` learns the chain (`TNum(c) → TFn(c,1)`, `TFn(c,m) → TFn(c,m+1)`);
  `ta_app` learns call assembly (`TFn`/`TPart` + a value → extend; the
  `k`-th argument saturates into
  `TExp(PCall(c, args, pre), RLoc(len), len+1)`); everything else still
  declines through the same defaults.

**Numbering convention (the file's convention 3, stated in its header): in
the walker's emitted `Ir`, callee 0 is the enclosing function itself and
callee `c ≥ 1` is the `c`-th distinct foreign callee in first-marking
order.** `PSelf` has always rendered `LetCall(0, …)`; that now reads as
"self", not "the single-function slice". This numbering is the *walker's own
coordinate system*, deliberately independent of the program-closure indices
the certificates use: the readback maps `0 → self`, `c → callees[c-1]` into
`FnIr`'s callee *names*, and the shared emitters downstream compute the
closure (callees' closures prefix-compatible, self last) exactly as the Rust
path always has. So the emitted file — the thing the cross-check compares —
is byte-identical between paths, while the library never has to be told how
many callees exist before the walk (which is what keeps the
`certgen.transcribe` slot signature unchanged).

The self-call is still the ih marker → `PSelf`; a foreign call is a callee
marker → `PCall`. Multiple calls, nested calls (`add(a, add(b, c))`) and
numeral arguments all compose through the same helpers; the "never
concatenates two prefixes" note in the file becomes historical and the
composition is the ordinary shift-and-append the original design sketch
predicted.

## 5. The Rust rim: what changes, what is frozen

- `certgen.rs::mark` handles `App`-spines with a global head (recurse) and
  `GlobalTm` (mint a callee marker via the resolution above). Its behavior on
  global-free bodies is byte-identical — the frozen-walker discipline of
  `issues/retire-rust-transcriber.md` stage 1 binds the *Compiler*, and this
  pass was always the elaborator's, but the same care applies.
- `marked_body` returns the callee table beside the marked body;
  `Elaborator::fn_body_code` wraps it (public, boxed) as §2's contract.
- Readback: `chain_from_rir` accepts `LetCall(c)` for any in-range `c`,
  resolving through the callee table into `Instr::Call { callee: name, … }`
  with the spec derived as before (`name(args…)`); out-of-range tags
  decline. `has_self_call` means callee 0 only, so the structural checks
  (no self-call in the zero arm, etc.) are unchanged in meaning.
- `generate_in_language` consumes `fn_body_code` and threads the table; the
  agreement gate, the slot spine, the Reader and its budget are unchanged.
- The Rust `Compiler` is not touched (frozen). It remains the byte-level
  oracle for mul until `retire-rust-transcriber` stage 2 deletes it.

## 6. What the tests pin

Per `docs/testing-generated-terms.md`'s axes, noting this round's artifacts
are walker data + an emission, so the axes land as: positive/negative
controls on the *walker* (library refl pins), end-to-end agreement on the
*emission* (byte equality with a path that is itself kernel-checked
end-to-end), and declines that name their deciding party.

- **Library pins** (`lib/certgen/certgen_code.hthr`, elaborated with the file):
  `mul`'s transcription written out — markers spelled as the walker builds
  them, expected `Ir` in the walker's own numbering (`LetCall(0)` self,
  `LetCall(1)` the callee) — checked by `refl` against what the Rust
  `Compiler` emits for the same function, modulo the readback renumbering;
  a partial application declines (`TPart` is not a value); a bare callee
  chain declines (`TFn` is not a value).
- **The positive**: `generate_in_language` on `mul` (with `add`'s emission in
  the context) produces an emission byte-identical to the frozen Rust v2
  path's — the same standard the transcriber round used for `add`/`dbl`/
  `third3`, and the Rust `mul` emission is already checked end-to-end by the
  expensive acceptance test, so byte-equality inherits that check.
- **Negative controls**:
  - a **body-less global**: `fn_body_code` on a theorem declines with the
    stated policy's message (the pin the charter asks for);
  - a call to a fn with **no generated instance** in the context declines
    downstream with the existing closure message (the in-language path now
    gets far enough to reach it — previously it declined at marking);
  - the existing perturbed-transcriber and perturbed-signature controls
    stay: a wrong library is refused by its own theorems, then by the
    kernel; a verdict drift is a loud `disagreement`, never a silent
    fallback;
  - the neutrality decline test (`mul` declines by naming the global) is
    **retargeted, not deleted**: its assertion flips to the positive above,
    and the decline shape it guarded (a global the path cannot serve) is
    re-pinned by the body-less-callee decline.
- **No regression**: every existing fixture (`add`, `dbl`, `seven`,
  `third3`, all declines, the Rust path with no library loaded) unchanged.

## 7. Declined and deferred, with homes

| What | Why not here | Home |
| --- | --- | --- |
| A recursor branch for `u^δ`/`U^δ` (route A) | Shared-notion edit across ch. 06/07, and identity-opaque anyway (§1) | Rejected, not deferred; re-opens only with an intensional-analysis theory round that would have to argue against hu2024layered's blocking |
| Kernel δ at layer c | Breaks code-does-not-compute and the definitions round's pins (§1) | Rejected |
| An explicit `unfold` former at layer m | Shared-notion round with no current customer; the harness hands over whole bodies (§1) | `issues/generators-in-the-language.md`, if a mid-walk customer (an analyzer discovering code values it must open) ever appears |
| Callee *bodies* inside one walk (true inlining-for-analysis) | No customer: transcription wants identity, not contents; contents are a second `fn_body_code` call by the harness | The guard/inj generator rounds (blockers (2)–(3)) decide if they ever need more than per-name pulls |
| `U^δ` in analyzed types | Fragment types are `Nat`-chains; a `U^δ` declines via the default arm (§3) | With the first non-`Nat` embedding (transcriber design §8 item 2) |
| Unforgeable marker heads | Fragment still contains no genuine `App`/`Lam`; the recognizer stance stands | `issues/code-variable-analysis-api.md` (the branded-token note) |
| In-language marking (both conventions) | Wants closed-substituend substitution sugar + meta re-entry, as before; convention 3 adds nothing new to that bill (it is the same rename-to-closed-terms operation) | `issues/code-variable-analysis-api.md` |
| Deleting the Rust walker | This round unblocks stage 2; the deletion itself owes the four-cover confirmation recorded there, and is the coordinator/user's call | `issues/retire-rust-transcriber.md` |
| Reasons in declines, user-declared analyzer slots, Ψ-resident meta defs | Unchanged deferrals of the two predecessor rounds | As recorded there |

## 8. Acceptance

1. `Elaborator::fn_body_code` exists as §2's contract (public, pull,
   marked+boxed, callee table, body-less decline) and
   `generate_in_language` consumes it; `fn_type_code` unchanged in interface
   with its placeholder comment corrected.
2. Callee markers per §3: `mark` closes Ψ-referencing fragment bodies;
   nullary and body-less callees decline at marking with messages naming the
   policy.
3. `lib/certgen/certgen_code.hthr` gains `PCall`, `TFn`, `TPart`, the composition
   helpers, and the `mul` + decline pins; both shells and both slot
   signatures byte-unchanged; the file still elaborates whole.
4. **The customer**: `generate_in_language` serves `mul` with an emission
   byte-identical to the frozen Rust v2 path's, and the retargeted test
   asserts it (with `add` in the generation context). Rust-path behavior
   with no library loaded unchanged.
5. Negative controls of §6, each with its message asserted; no existing
   fixture regresses.
6. **No kernel diff at all** — the metatheory obligation of this round is
   the empty set, checked by `git diff --stat crates/kernel` being empty.
7. Full `scripts/test` green, both whole-library acceptance tests included.

## 9. What changed in contact with reality

Small, because the design was written against a hand-computed walk of `mul`
(§4's numbering worked example was verified instruction by instruction before
any code moved). Three contacts:

1. **The spec-spelling divergence caught `mul`, in a predicted class at an
   unpredicted spot.** The first byte-comparison failed on exactly one
   difference: the fixture's zero arm was the literal `0`, which the
   source-reading Rust path spells `0` and the source-blind walker derives as
   `Zero` — `seven`'s recorded divergence (transcriber design §10.5), riding
   along on the new fixture. Everything structural — IR, closure, program,
   both certificates — was byte-identical on the first run. Resolution: the
   `MUL` fixture spells `Zero`, with the test comment stating why (byte
   identity should test what `mul` is *for*, the cross-function call, not
   re-pin `seven`'s divergence); the alternative — elaborating a second,
   renamed in-language `mul` emission in the expensive acceptance test —
   would have bought a duplicate of an already-checked certificate for
   ~doubled `mul` cost.
2. **The library's no-`let` style shaped the call assembly** into
   `ta_call`/`ta_call_fin` (merge, then decide saturation) instead of one
   function with intermediate bindings. Behavior as designed; the §4 helper
   list otherwise landed one-for-one, and the transcriber file's "never
   concatenates two prefixes" note is now historical exactly as §4 predicted.
3. **Nothing else moved.** No kernel diff (`git diff --stat crates/kernel`
   empty, acceptance 6); both shells, both slot signatures, and every
   existing fixture unchanged; the fast lane passed whole on the first
   post-change run. The §2 correction to `fn_type_code`'s "placeholder"
   comment was applied as written.
