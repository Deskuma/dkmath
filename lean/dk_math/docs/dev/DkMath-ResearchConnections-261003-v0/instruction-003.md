# DRC-003 — Cyclic determinant norm

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Find and kernel-check the cleanest reusable cyclic-algebra statement behind the
Cosmic Formula.

The intended mathematical picture is that a cyclic shift operator carries the
full power-difference determinant

~~~text
det (z I - u S) = z^n - u^n,
~~~

and therefore, after setting `z = g + u`,

~~~text
det ((g + u) I - u S) = g * GN n g u.
~~~

This should expose the complete Cosmic Formula carrier as a cyclic norm /
determinant object, not merely the quotient-like GN shell.

## What to do

Treat this as an open design-and-formalization task.

- Audit DkMath and pinned Mathlib for existing cyclic-shift, circulant,
  permutation-matrix, determinant, quotient-ring, and AKS cyclic-quotient
  infrastructure.
- Reuse existing DkMath objects where that produces a natural theorem. Avoid a
  parallel cyclic theory merely to match the conceptual formula above.
- Choose the most reusable representation and theorem statement yourself.
- Establish the strongest clean theorem that the current APIs support for
  arbitrary cycle length in the natural nonempty/positive range.
- Connect it explicitly to the current Cosmic Formula / GN / GTail API.
- Keep the full determinant/power-difference carrier distinct from the prime
  cyclotomic-shell field norm already present elsewhere in DkMath.

The exact carrier type, namespace, theorem names, proof method, determinant
technology, and typeclass assumptions are for you to determine.

## Expected mathematical result

A successful Outcome A should leave DkMath with a production-level theorem
showing that the relevant cyclic determinant/norm recovers

~~~text
z^n - u^n
~~~

and a checked specialization recovering

~~~text
g * GN n g u.
~~~

A mathematically equivalent formulation is acceptable if it integrates better
with the existing AKS or cyclic-quotient infrastructure.

The theorem should be genuinely general in `n`, not a finite set of checked
ranks.

## Boundaries

Do not:

- replace a general theorem by finite determinant computations;
- introduce division when a polynomial/determinant formulation avoids it;
- identify the full cyclic determinant with a prime cyclotomic field norm;
- duplicate an existing cyclic quotient or AKS carrier without a clear reason;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty merely because this connection is newly exposed
  in DkMath.

If the exact conceptual formula is blocked by indexing, sign, parity, or a
different canonical representation, determine the correct statement and report
the discrepancy rather than forcing the requested syntax.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- meaningful boundary/regression cases;
- public API integration where appropriate;
- axiom audit;
- full build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-003.md
~~~

with Outcome A / B / C, the representation chosen, the actual theorem obtained,
its relation to GN/Cosmic Formula and existing AKS/cyclotomic infrastructure,
validation results, and any mathematical or API obstruction.

Do not finish the checkpoint without a report, even if the intended theorem
needs to be revised.
