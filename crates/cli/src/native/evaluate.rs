//! A closed `List<Nat>` read back from the kernel's evaluator: how a producer
//! learns the bytes of a library definition it must publish (the command's
//! layout, `elf64_command`'s `command_code`), instead of restating the
//! library's encoders here. A reader, not a judgement: the certificate states
//! the same bytes as literals and the kernel re-checks them against the
//! definition, so a misread list is refused there.
use heather_elab::Elaborator;
use heather_kernel::eval::Eval;
use heather_kernel::reduce::Defs;
use heather_kernel::term::GlobalBinding;
use heather_kernel::value::program::ContextProgram;
use heather_kernel::value::{Env, TmClo, Val, ValueArena};

// Enough for a file-sized layout; a list that needs more is a producer bug.
const FUEL: u64 = 1 << 34;

/// The value of the most recently declared global, a nullary `fn … →
/// List<Nat>`, element by element. A user inductive is a finitary W-node
/// (`sup_f`): a list's label is `inl` for `Nil` and `inr(⟨tag, ⟨head, ⟨⟩⟩⟩)`
/// for `Cons`, and its one child, the tail, is the first of its children.
pub(super) fn last_nat_list(elab: &Elaborator) -> Result<Vec<u64>, String> {
    let psi = elab.psi();
    let Some(GlobalBinding::Tm { body: Some(body), ctx, .. }) = psi.bindings.last() else {
        return Err("the last declaration is not a definition".into());
    };
    if ctx.entries.len() != 0 { return Err("the last declaration takes arguments".into()); }
    // Stored in its own Ψ-prefix: one binding short of the ambient Ψ.
    let body = std::sync::Arc::new(body.shift_global(1));
    let arena = ValueArena::new();
    let mut ev = Eval::new(FUEL, Defs::transparent(psi), ctx.base, &arena);
    let stuck = |what: &str| format!("the list's {what} did not evaluate to a constructor");
    let mut node = ev.eval_tm(&body, &Env::identity(&arena, 0)).map_err(|_| "out of fuel".to_string())?;
    let mut out = Vec::new();
    loop {
        node = ev.delta_whnf(node).map_err(|_| "out of fuel".to_string())?;
        let Val::Supf { label, children, .. } = &*node else { return Err(stuck("spine")) };
        let (label, children) = (*label, *children);
        let payload = match &*whnf(&mut ev, label)? {
            Val::Inl { .. } => return Ok(out),
            Val::Inr { val, .. } => *val,
            _ => return Err(stuck("label")),
        };
        // ⟨tag, ⟨head, ⟨⟩⟩⟩
        let Val::Pair { snd: fields, .. } = &*whnf(&mut ev, payload)? else { return Err(stuck("payload")) };
        let fields = *fields;
        let Val::Pair { fst: head, .. } = &*whnf(&mut ev, fields)? else { return Err(stuck("fields")) };
        let head = *head;
        out.push(nat(&mut ev, head)?);
        let Val::Pair { fst: tail, .. } = &*whnf(&mut ev, children)? else { return Err(stuck("children")) };
        let tail = *tail;
        node = ev.force(tail).map_err(|_| "out of fuel".to_string())?;
    }
}

fn whnf<'v>(ev: &mut Eval<'_, 'v>, c: &'v TmClo<'v>) -> Result<std::sync::Arc<Val<'v>>, String> {
    let v = ev.force(c).map_err(|_| "out of fuel".to_string())?;
    ev.delta_whnf(v).map_err(|_| "out of fuel".to_string())
}

// A Nat as `heather_kernel::eval::nat_value` reads one, from a closure.
fn nat<'v>(ev: &mut Eval<'_, 'v>, c: &'v TmClo<'v>) -> Result<u64, String> {
    let mut total = 0u64;
    let mut next = c;
    loop {
        let v = whnf(ev, next)?;
        next = match &*v {
            Val::Zero => return Ok(total),
            Val::Succ(pred) => { total += 1; *pred }
            Val::NatRun { program, tail } => {
                total += ContextProgram::repetition_count_up_to(program, u64::MAX - total).ok_or("a count past u64")?;
                *tail
            }
            _ => return Err("an element did not evaluate to a number".into()),
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The reader on a list built by a library function, with an element that
    // computes, and on the empty list.
    #[test]
    fn a_closed_list_reads_back() {
        let mut elab = Elaborator::with_prelude().unwrap();
        for (name, src) in [
            ("logic", include_str!("../../../../lib/std/logic.hthr")),
            ("bool", include_str!("../../../../lib/std/bool.hthr")),
            ("nat", include_str!("../../../../lib/std/nat.hthr")),
            ("option", include_str!("../../../../lib/std/option.hthr")),
            ("pair", include_str!("../../../../lib/std/pair.hthr")),
            ("list", include_str!("../../../../lib/std/list.hthr")),
        ] {
            elab.elab_module_source(name, src).unwrap();
        }
        elab.elab_module_source("probe", "import list; import nat;\nfn probe() → List<Nat> { List::append([1, 2, 300], [Nat::pow(2, 20)]) }")
            .unwrap();
        assert_eq!(last_nat_list(&elab).unwrap(), vec![1, 2, 300, 1 << 20]);
        elab.elab_module_source("empty", "import list; import nat;\nfn probe() → List<Nat> { [] }").unwrap();
        assert_eq!(last_nat_list(&elab).unwrap(), Vec::<u64>::new());
    }
}
