# Getting started

Heather source files use the `.hthr` extension. From the repository root,
build the checker, then check a file with:

```console
$ cargo build --release --bin heather
$ target/release/heather check path/to/file.hthr
```

For repository development, follow `CLAUDE.md`: direct checker runs must be
resource-capped, and the test suite is run through `scripts/test`.

## A first file

```heather
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}

fn double(n: Nat) -> Nat {
    add(n, n)
}

theorem two_plus_two(): add(2, 2) = 4 {
    refl
}
```

Declarations are visible in source order. Adjacent mutually recursive
declarations are the exception: Heather recognizes their recursive call graph
as a group.

`fn` declarations are transparent and may compute. `theorem` declarations
are checked and then kept opaque. `refl` succeeds when both sides of an
equality are definitionally equal, including equality discovered by reducing
transparent functions.

The complete [`language_tour.hthr`](examples/language_tour.hthr) example is
checked as part of documentation verification.

## Imports

```heather
import logic;
import nat::{Le, le_refl};
```

Imports must precede declarations. A module is a `.hthr` file named by its
file stem. The checker searches the importing file's directory and every
`-L` directory; from the repository root it also uses `lib/std` by default.

`import nat;` enables qualified and resolvable unqualified access to the
module. `import nat::{Le};` additionally selects the listed name when several
imports would otherwise make it ambiguous. It is not a restrictive import.

## Formatting and editor support

```console
$ target/release/heather fmt file.hthr
$ target/release/heather fmt --check file.hthr
```

The repository contains a Zed extension under `editors/zed`. Comments begin
with `//` and continue to the end of the line.
