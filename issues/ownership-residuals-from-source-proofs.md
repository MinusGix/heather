---
title: Discharge a checker's residual from the proof the source carries: the pin, the shape of the term, the kernel's cost
status: closed
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first of three untested points in `docs/language/ownership-design.md` §18.4: discharging a residual obligation from the proof the source already carries. The design's sixth stage (every `runtime fn` moved to the new pipeline) stands on it, and every experiment so far discharged its residuals with a hand-written term and `omega`.

## Scope

- **Source functions that carry their proofs**, written as ordinary Heather over lists: one that reads an element under a parameter proof (`inside: ∥i < xs.len()∥`, the arena's `read` in miniature); one that writes an element while holding a view of a later window, its apartness from a hypothesis of an `if`; one that calls another and passes its own proof on.
- **Each one's body by hand in the checker's language** (`lib/lang/ownership/call_check.hthr`, extended only if a residual kind is missing: a bound, `Below(i, n)`).
- **The pin**: the reflected body's meaning equals the function, by conversion.
- **The discharge**: each residual, stated at the reflected environment's words, proved from the source function's own hypothesis through the pin. The proof term must have a mechanical shape a generator could emit from the function's elaborated body (which holds the proof at that site, in that context): say what the shape is.
- **Cost**: what the kernel pays to convert the residual's statement to the hypothesis's, per site and as the body grows (measure at doubling sizes, `docs/proof-patterns.md` §7).

## What refutes the design

The discharge is not a short term of a fixed shape; or the conversion's cost grows faster than the body; or a proof that reads a `let`-bound value (see [[found-proof-over-let-bound-read]]) cannot be carried.

## Done when

The three functions have their pins and their soundness theorems with no hand proof beyond the mechanical shape, the cost is reported as a shape, and the log says what a generator must emit per site.

## What it assumes from elsewhere

- **[[ownership-checker-call-and-write-view]]** (closed) gives the language, residuals and `check_sound`.
- **[[ownership-checker-loans-and-joins]]** is extending that module; this issue adds probes and at most a residual kind.

## Log

- 2026-11-25: 2026-11-25: Built and measured. `lib/lang/ownership/site_facts.hthr` (over `call_check`, which it does not touch), probes in `lib/_tests/lang/ownership/site_facts_tests.hthr`. **Result: the design works; the discharge is the source's own proof, by conversion, for bounds and callee preconditions; apartness needs `omega`; and a function with many residuals must be discharged by one ascription of a restated conjunction, not component by component, or the cost is quadratic.**

  **What the checker's module lacked, and `site_facts` adds** (each the smallest that let a source proof reach a residual):
  - `Fact = Owe(Owed) | Inside(x, i)`: a residual stated over the meaning's *final state* (every version and every word), not over its words alone, and in the source's vocabulary. `Inside(x, i)` is an element read's bound, `∥i.val(words) < list_at(objs, x).len()∥`: a squashed `Lt`, the type a source writes for an erased index proof. `bounds` emits one per `Get`; `check_site = check_fn`'s residuals ++ bounds. The fragment's run reads zero past a reference, so agreement holds without the bound and `site_sound` drops it; it is what the bytes level owes.
  - `FnSafeAt`: `FnSafe` whose precondition is over `(arg, ws)`, not `ws` alone. `pick`'s `inside: ∥i < xs.len()∥` is not a `FnSafe` precondition (it reads the list). `site_sound` is `check_sound` at one argument (`check_body_sound` was pointwise already, so it is `check_sound`'s twenty lines with the precondition widened).
  - `words_eta`/`at_words`: `check_sound` asks for residuals at *open* words `ws`, where the meaning's spine `ws ++ [x]` is stuck and no word reads off it. `words_eta(ws, n, e: ws.len() = n): ws = spell(ws, 0, n)` (`[word(ws, 0), …]`), and `at_words` moves a discharge stated at the spelled words to open ones. One lemma for every function, so a generator states each discharge at the source's locals.
  - `Branch(a, b, yes, no)`: `if h: a <= b` over the given words, each arm a whole straight body (the prefix repeated), meaning a `convoy` on the test's bit, the very shape the source's `if h:` elaborates to (`poke_reflects` is `refl`). `branch_sound` takes each arm's `FnSafeAt` under `pre ∧ bit = side`.

  **The probes**: `pick` (read under a parameter proof), `hop` (`let j = xs[i]; xs[j]`, the second bound over a let), `hop_if` (`let j = xs[i]; if h: j < xs.len() {…}`), `poke` (view, then a write under `if h: k <= j`), `after_read` (the view's length a let-bound read), `shift`/`outer` (a call passing `h` on; the program's theorem at every depth by `prog_sound`), `outer2` (the callee's word a let-bound read, the caller's proof over the read). Each has its pin by `refl`, its `check_site` verdict by `refl`, its discharge at the source's locals, and its safety from `site_sound`/`branch_sound`/`prog_sound` with nothing else. Controls: `hop_control` (the bound fails at `xs = [5]`), `poke_yes_control` and `poke_yes_differs` (the arm without its test: residual false at `k = 1, j = 0`, the run reads 9 and the meaning 5), and `hop_wrong_site` (`// expect-error(kernel)`: the first read's proof cited at the second read's site is refused, NotConvertible).

  **1. The shape.** Per function, a generator emits:
  ```
  f::pre(arg, ws)  := the source's hypotheses, each parameter replaced by its reading (the list by arg, the k-th word by word(ws, k))
  f::reflects      := mean_fn(w, f::r, xs, [x₀, …]) = f(xs, x₀, …, h…)        by refl
  f::site(w, xs, x₀…, h…) : Fact::All(f::rs, pres, mean_body(w, f::r.body, Sem([xs], Nil, [x₀, …])))
                   := ⟨p₁, ⟨p₂, … ⟨p_R, trivial⟩…⟩⟩
  f::safe(w)       := site_sound(sigs, pres, f::r, f::rs, refl, f::pre, w,
                          at_words(w, f::r.body, f::rs, pres, f::pre, n, λ arg ws h => f::site(w, arg, word(ws, 0), …, h.1, …)),
                          callees)
  ```
  and `p_r`, per residual, by kind:
  - a bound (`Inside`) or a callee's precondition (`Pre`): **the proof term the source has at that site, unchanged**, the kernel converting the residual's statement at the reflected words to the hypothesis's statement at the source's locals. The same for all three origins; only how the source binds it differs: a parameter (`inside`, `h`), `decide_true<P>(e)` of the enclosing `if`'s convoy equation `e` (`poke_safe`, `hop_if_site`), or a `squash` of either.
  - apartness (`Due(Spans(…))`): `let s: S = omega(h₁, …); s` where `S` is the verdict with each atom read as a source term (`Span(0, k).apart(Span(j, 1)).IsTrue()`). Not a conversion: the residual is a Boolean verdict over a disjunction, spelled with the view's offset (`0 + k <= j`, and `Nat::add` recurses on its right), against the source's `k <= j`. So for apartness a generator needs the hypotheses *in scope* at the site, not only an argument at the site (the source's write takes no apartness proof: the checker asks it).
  For a branch, `f::safe` is `branch_sound(br, sig, pre, w, site_sound(… yes …), site_sound(… no …))`, the `if`'s proof inside the arm being `decide_true<P>(h.right)`.
  For many residuals, the measured shape is the **restated** one (point 2): `f::restated(xs, x₀…) : Type := ∥…∥ ∧ (… ∧ True)`, the residuals' statements at the source's terms, and `f::site := (let r: f::restated(…) = ⟨p₁, …⟩; r)`, one ascription (`hop_site_restated`).

  **2. The cost.** Kernel steps, each run on a fresh copy of a library-only warm store (a reused store answered a repeated item 16× cheaper: `docs/proof-patterns.md` §7 matters here). Generated bodies of `N` statements (`Get`s and view reads), with the pin, the verdict, the site and the assembled theorem as separate items:
  - *One residual at the end* (`N` reads through a view, then one bounded read): the site costs 1.2k, 1.5k, 2.0k, 3.1k, 5.2k, 9.4k, 19.4k at N = 8 … 512: **linear, about 37 steps a statement**, which is evaluating the meaning to the final state (lazily: the residual reads word 0, so the snoc spine is peeled once). The verdict `check_site(…) = Some(…)` is linear too (81k at 512); the assembled `site_sound` application is linear (22k at 512).
  - *A residual at every statement* (`N` bounded reads): the site costs 10.6k, 40.6k, 212k, 1.38M, 3.81M, 10.4M at 8 … 256 (4.2 s at 256, all in the gate): **quadratic, about 160·N² steps**. The same with a let-bound last index (`endlet`): the same curve. At 512 the surface tuple hits the elaborator's nesting limit (512), a syntax limit, not the kernel's.
  - *Where it is.* Not in reflection's correspondence: with the final state written out once (`f_state`) and proved equal to the meaning (`f_pin`: 3.6k at 16, 23k at 64), the tuple at the written-out state still costs 1.24M at 64. The tuple's components are converted one at a time, each against the state it reads, and nothing one computes is kept for the next: each residual re-runs the meaning (or re-instantiates the written-out state's body). Threading the state through a recursive predicate (`along`) did not help (1.5M at 128).
  - *The fix, measured.* Restate the residuals at the source's terms and move the conjunction by **one** ascription: the whole-conjunction conversion costs 5.5k, 37k, 45k, 62k at 16, 64, 128, 256: **linear**, 170× cheaper at 256 (28 ms). One conversion shares the meaning's evaluation across the residuals. The elaborator's check of the surface tuple against a literal conjunction is superlinear (1.7 s at 256, the gate 21 ms), which a generator writing kernel terms does not pay. A cons lemma with implicits (`all_cons`) made the gate 3× cheaper but the elaborator's unification of its implicits took 4.8 s at N = 16: not usable from source.
  - *The pin* (`mean_fn(…).word = f(…)` by `refl`) is **quadratic in this fragment**: 1.0k, 1.9k, 4.6k, 13.9k, 47.8k, 177k, 683k at 8 … 512 (0.37 s at 512). The meaning keeps its words as a snoc list (`words ++ [x]`) read by position, so reading the last word walks every append. A representation of the meaning's, not of the design: §4.3's pin is linear because its interpreter's environment is not a snoc list.
  - *Per site in the probes*: a bound or a precondition 0.95k to 2.9k steps; apartness by `omega` 5.6k to 7.5k.

  **3. A proof over a `let`-bound value carries.** `hop` (the second read's index is word 2, bound by the first read; `next: ∥xs[i] < xs.len()∥` discharges it), `hop_if` (`if h: j < xs.len()` after `let j = xs[i]`: the elaborated `let` is its value, so `h: xs[i] < xs.len()`, and `squash(decide_true(e))` discharges the bound), `outer2` (the callee's word a read, the caller's `h: xs[0] <= j` is the precondition at the call's words), `after_read` (`omega` reads `xs[0]` as an atom). Nothing is spelled: the reflected word evaluates to the same term the elaborated `let` inlined. [[found-proof-over-let-bound-read]] is a *found* proof (a tactic must spell the read in a hygienic context); a *carried* one never spells it. Apartness over a read goes through `omega` in an ordinary theorem; it would meet that issue only inside a `runtime fn`'s hygienic default.

  **4. What reflection must keep.** Per residual: (a) the site's proof term as the elaborated body has it (an erased argument of a read or a call; `decide_true(e)` of an enclosing convoy, so the convoy's equation binder per `if`); (b) for apartness, the hypotheses in scope at the site with their types, since the write has no proof argument; (c) the correspondence of the reflected words to source terms: a parameter word `k` is `word(ws, k)` (what `at_words` spells), a let-bound word is the `let`'s value, needed only to write the restated conjunction and the `omega` ascription; the conversion itself re-derives it. Nothing needed is missing from the elaborated body: the values of `let`s are there (inlined), the proofs are there as arguments or binders. What is *not* in it is a choice of reflection: an `if` reflected as two straight bodies repeats the prefix.

  **5. What the design must change** (none refutes it):
  - Residuals are propositions in the source's vocabulary (a squashed `<`, the callee's precondition), stated over the meaning's final state. A Boolean verdict is fine for the checker to decide closed cases, but the open residual should be the proposition, so the discharge is the proof. Apartness is a disjunction; a residual that names the side (`Before(lo + n, i)`, `After(…)`) would make it a conversion too, with `omega` only for the arithmetic spelling.
  - A precondition reads the parameters' values, not only the words (`FnSafeAt`), and `Pre` at a call must state the callee's precondition at the lent window's value: the arena's `read(h, inside: h < heap.len())` as a callee is not statable today. With it, the call contract is one statement, not one per call shape.
  - The discharge is asked as one statement a generator ascribes at once, the residuals restated at the source's terms (the measured linear route). Per site, the generator emits only the proof term.
  - The meaning's environment should not be a snoc list read by position (the pin's quadratic).
  - An `if` whose test reads a word the body bound needs the checker's own branch (run and meaning agree on that word by `Sim.words`, which `FnSafe` does not export): [[ownership-checker-loans-and-joins]]'s branch.

  Not built, said by name: `pick` as a callee (no call of a reader answering a word in the fragment; its precondition reads its list), and a test over a let-bound word assembled into a function's safety. Residue: [[ownership-residual-discharge-restated]] (the restated discharge as the checker's interface, and its elaborator cost), [[ownership-site-facts-into-the-checker]] (the four additions, folded into the one checker), [[ownership-meaning-word-spine]] (the pin's quadratic).
