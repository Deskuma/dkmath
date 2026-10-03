# DRC-004 — Prime cyclic glue

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

For prime cycle length, identify and kernel-check the cleanest integral gluing
principle behind the decomposition of the cyclic carrier into the trivial
character part and the cyclotomic part.

The intended arithmetic picture is the compatibility square

~~~text
Z[C_p]  ->  Z[zeta_p]
  |             |
  v             v
Z       ->      F_p,
~~~

with the two components glued by the common residue condition modulo p.

This checkpoint should turn that picture into a reusable DkMath theorem/API,
using the representation that best fits the existing repository.

## What to do

Treat this as a design-and-formalization task.

- Audit DkMath and pinned Mathlib for the existing AKS cyclic quotient,
  cyclotomic quotients/rings of integers, augmentation/evaluation maps,
  quotient maps, residue maps, and any pullback/fiber-product infrastructure.
- Reuse existing objects whenever possible; avoid creating a second model of
  the same cyclic or cyclotomic algebra just to match the schematic square.
- Determine the strongest clean integral reconstruction/gluing theorem that is
  actually supported by the current APIs.
- Make the compatibility condition explicit.
- If natural, include the p-th-power gluing consequence: compatible components
  that are genuine p-th powers should reconstruct a genuine p-th power in the
  cyclic carrier, with any required hypotheses stated precisely.
- Keep unit-times-p-th-power statements distinct from genuine p-th powers.
- Connect the result to the cyclic determinant/Cosmic carrier when that
  connection is natural, but do not force downstream FLT consequences here.

The exact carrier, theorem statements, namespaces, maps, and proof strategy are
for you to determine.

## Expected mathematical result

A successful Outcome A should leave DkMath with a production-level prime cyclic
gluing API showing, in some mathematically equivalent form, that the integral
cyclic object is recovered from compatible trivial-character and cyclotomic
components, and that the compatibility is controlled modulo p.

If the full fiber-product equivalence is unnecessarily heavy, a smaller
reconstruction theorem with the same arithmetic content is acceptable and may
be preferable.

## Boundaries

Do not:

- assert a fiber-product/Milnor/Rim square stronger than what is actually
  kernel-checked;
- identify equality of norms with equality of elements;
- erase the congruence compatibility condition;
- promote unit-times-p-th-power data to a genuine p-th power without controlling
  the unit;
- duplicate existing AKS/cyclotomic carriers without a clear reason;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty from this repository connection alone.

If the schematic square above is not the best formal representation in the
current library, choose the correct one and explain why.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- meaningful prime/boundary regressions;
- public API integration where appropriate;
- axiom audit;
- full build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-004.md
~~~

with Outcome A / B / C, the representation chosen, the precise compatibility
and reconstruction theorem obtained, its relation to AKS/cyclotomic/Cosmic
infrastructure, validation results, and any remaining obstruction.

Do not finish the checkpoint without a report.
