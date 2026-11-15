# Setoids, lifting, and relational transfer: reading guide

Collected for the 2026-09-04 design discussion. This guide indexes sources and
implementation questions; decisions and acceptance criteria live in the issues.
The Lifting/Transfer paper and the refinement papers below were already present
from the data-representation discussion. They are reused, not downloaded twice.

## Primary reading

1. Brian Huffman and Ondřej Kunčar, *Lifting and Transfer: A Modular Design for
   Quotients in Isabelle/HOL* (CPP 2013).
   [Local PDF](papers/lifting-transfer-huffman-kuncar-cpp2013.pdf) ·
   [Author-hosted source](https://www21.in.tum.de/~kuncar/documents/huffman-kuncar-cpp2013.pdf).
   Read for the separation between relational theorem transfer and operation
   construction, and for a common treatment of quotients and subtypes. Inspect
   which construction steps need representation maps or logical assumptions
   before adapting the design to Heather.

2. Matthieu Sozeau, *A New Look at Generalized Rewriting in Type Theory*
   (Journal of Formalized Reasoning 2(1), 2009; published online 2010).
   [Local author preprint](papers/generalized-rewriting-sozeau-2009.pdf) ·
   [Author-hosted source](https://sozeau.gitlabpages.inria.fr/www/research/publications/A_New_Look_at_Generalized_Rewriting_in_Type_Theory.pdf) ·
   [Publication](https://doi.org/10.6092/issn.1972-5787/1574).
   Read for compositional compatibility proofs, higher-order rewriting,
   polymorphism, and subrelations. Ask how much relation and certificate
   plumbing can disappear from ordinary calculation proofs.

3. Jean-Philippe Bernardy, Patrik Jansson, and Ross Paterson, *Proofs for Free:
   Parametricity for Dependent Types* (JFP 22(2), 2012).
   [Local PDF](papers/proofs-for-free-bernardy-jansson-paterson-2012.pdf) ·
   [Author-hosted source](https://www.staff.city.ac.uk/~ross/papers/proofs.pdf) ·
   [Publication](https://doi.org/10.1017/S0956796812000056).
   Read for relational translations that produce proofs from terms in pure
   type systems. The Heather research question is per-function certified
   parametricity with explicit support for modal/contextual code and its
   observers; the paper does not establish that result for Heather.

The latter two PDFs were downloaded from the listed author-hosted sources on
2026-09-04. The existing Lifting/Transfer PDF was checked during this round.

## Adjacent references already in docs

- [CoqEAL / Refinements for Free](papers/coqeal-refinements-for-free-cpp2013.pdf).
- [Lammich / Automatic Data Refinement](papers/autoref-lammich-itp2013.pdf).
- [Fiat / ADT synthesis](papers/fiat-adt-synthesis-popl2015.pdf).

These were collected by [datarepr-separation](../issues/datarepr-separation.md).
Consult them when connecting semantic transfer certificates to implementation
refinement; this round does not re-charter executable representation synthesis.

## Work ownership and sequence

Start with the [relational core](../issues/relational-transfer-core.md) and
[manual setoid API](../issues/setoid-core-api.md), exercising the first
[relation-indexed algebra](../issues/relation-indexed-algebra.md) customer.
Keep [dependent transport](../issues/dependent-relational-transport.md) and
[subtype evidence](../issues/subtype-transfer-and-evidence.md) as early design
stress tests rather than waiting for a complete automation stack.

[Mathematical transport](../issues/setoid-morphisms-and-transport.md) supplies
manual constructions and comparison examples. [Proof generation](../issues/setoid-auto-lifting.md)
then reproduces those constructions; [certified parametricity](../issues/certified-parametricity.md)
extends its reusable relational certificates.

Agreed direction: relation-indexed algebra and compositional, kernel-checked
proof generation. Open experiments: equality notation, evidence reuse versus
squashing, and the smallest adequate dependent transport interface. No quotient
kernel extension, universal proof irrelevance, or blanket parametricity theorem
is introduced by this planning round.
