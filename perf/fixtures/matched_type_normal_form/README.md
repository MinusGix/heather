# The matched type argument's normal form

The measurement corpus of `issues/elab-emits-normal-form-of-matched-type-argument.md`
(and `issues/emit-ty-rewalks-normalized-type.md`,
`issues/parser-certified-composition-cost.md`): each file holds the same
certified parser component and varies one thing, which its header names.

- `t_cp1.hthr`: `parser_primitives::complete_post` verbatim, the base.
- `t_cp9.hthr`: the spec as `And<relation, True>`, the record instantiation at an open type.
- `t_qt2.hthr`, `t_qt1.hthr`, `t_cp9.hthr`, `t_qt3.hthr`, `t_qt5.hthr`: zero
  to five combinator layers over the same reply, the scaling curve.
- `t_qt4.hthr`: `t_qt3` with the reply named as a declaration.

They check on their own (`heather check -L lib -L lib/std <file>`, capped as
CLAUDE.md says); `t_qt5` wants a wider rail. The scripts and patches the
rounds measured them with were in `probes/` and are cited as
`probes/<file>@ef3961a`.
