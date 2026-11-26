---
title: A kernel error's report panics in subst (variable escapes the substitution's target) on a Π match arm
status: open
labels: [elaborator,kernel]
area: language
created: 2026-11-26
updated: 2026-11-26
---

Checking a `Type`-valued function whose match arm is a Π over a list's members, beside a sibling arm that is not, panicked in the kernel's substitution while the elaborator was building the report of a kernel error (`refusals::kernel_error` in the backtrace), instead of reporting the error:

```
thread 'main' panicked at crates/kernel-lib/../kernel/src/subst.rs:1798:9:
kernel invariant violated: local variable 14 escapes the substitution's target entries (variables cannot address a context-variable base)
```

## Reproduction (in the tree at the commit that files this)

A module beside `lib/lang/ownership/sound_local.hthr`, checked with `heather check --limits dev --cache`:

```
import logic;
import bool;
import nat;
import option;
import list;
import shape;
import body;
import level2;
import run;
import checker;
import sound_state;
import sound_local;

fn CSt::Synced2(tys: Nat → Type, strs: Strs(tys), s: CSt, e: Env(tys), m: Mach(tys), l: Nat) → Type {
    match s.role(l) {
        KView => match (s.ents(l)).any_bit(λ en => en.mode.writes()) {
            True => (en: VEnt) → Mem(en, s.ents(l)) → en.back = True → VEnt::Sync(tys, strs, s, e, m, en),
            False => VEnt::Any(s.ents(l), λ en => VEnt::Sync(tys, strs, s, e, m, en)),
        },
        KHold(_, _) => True,
        KPlain => True,
        KGone => True,
    }
}
```

Replacing the Π arm's last step `→ VEnt::Sync(tys, strs, s, e, m, en)` by nothing (ending at `en.back = True`) checks. Lifting the Π arm into a function of its own (`CSt::SyncedW` in `sound_local.hthr`, called from the arm) checks, which is how `sound_local` spells it. Three standalone shrinkings of the same shape (an inductive with a payload matched outside, a computed `Bool` matched inside, a Π over `Mem` in one arm and a `let`-bodied predicate in it) did not reproduce, so the trigger depends on something in `VEnt::Sync`'s context (its `let`, `Mach::ixs`, `Sel::read_at` at a computed environment).

Two defects, possibly one: the refusal's rendering must not panic (a kernel error is reported, whatever it is); and if the definition is well typed, the kernel should not refuse it.
