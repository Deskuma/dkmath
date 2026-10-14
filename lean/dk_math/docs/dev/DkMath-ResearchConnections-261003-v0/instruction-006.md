# DRC-006 — TraceOne residue-type classification

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Package the finite residue behavior of the existing quadratic/TraceOne carriers
as a clean split / inert / ramified classification, without conflating rings
that merely share the same additive group.

The guiding examples are:

~~~text
TraceOne, even s mod 2  -> split type
TraceOne, odd s mod 2   -> inert type
Gaussian mod 2          -> ramified dual-number type
~~~

and, more generally for odd residue characteristic, the quadratic discriminant
should control the split / inert / ramified behavior.

## What to do

Treat this as a structure-classification and API-design task.

- Audit the current TraceOne, Gaussian, quadratic-discriminant, residue,
  finite-field, quotient, and polynomial-factorization infrastructure in
  DkMath and pinned Mathlib.
- Decide on the smallest reusable notion that captures the three residue
  behaviors without identifying non-isomorphic multiplications on the same
  additive carrier.
- Kernel-check the strongest clean classification theorem supported by the
  current APIs.
- Make the mod-2 TraceOne parity dichotomy explicit.
- Include the Gaussian ramified mod-2 model when it integrates naturally.
- For odd primes, connect the quadratic discriminant to split / inert /
  ramified behavior when this can be stated cleanly and generally.
- Reuse existing signed/discriminant APIs rather than introducing competing
  definitions.

The exact representation, theorem statements, equivalences, namespaces,
finite-field models, and proof strategy are for you to determine.

## Expected mathematical result

A successful Outcome A should leave DkMath with a production-level residue-type
classification API that explains why superficially similar small carriers can
have different multiplication laws.

It should make precise, in some natural formalization, the distinction between

~~~text
split
inert
ramified
~~~

for the relevant quadratic residue algebras, with the TraceOne mod-2 behavior
as an explicit calibration.

A classification by factorization type or an equivalent algebraic formulation
is acceptable if it is more canonical than naming concrete finite rings.

## Boundaries

Do not:

- identify rings merely because their underlying additive groups have the same
  cardinality or additive structure;
- erase multiplication data when giving equivalences;
- infer a full ring equivalence from matching discriminants alone;
- force the mod-2 and odd-prime cases into one theorem if their natural APIs are
  genuinely different;
- duplicate existing quadratic/discriminant definitions without a clear reason;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty from this repository packaging alone.

If the requested concrete models are awkward in the pinned APIs, choose a more
canonical factorization/residue formulation and explain the translation.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- split/inert/ramified regressions;
- public API integration where appropriate;
- axiom audit;
- full build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-006.md
~~~

with Outcome A / B / C, the classification notion chosen, exact theorems
obtained, concrete model calibrations, validation results, and any remaining
obstruction.

Do not finish the checkpoint without a report.
