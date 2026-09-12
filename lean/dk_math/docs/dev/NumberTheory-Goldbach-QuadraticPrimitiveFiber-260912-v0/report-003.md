# QP-003 — exact LL/LR/RR accounting

Predecessor: QP-002 commit `f931c16cf`.

`choose_two_add` proves degree-two Vandermonde, including L=0 or R=0, by
Mathlib Pascal recursion. `localLL`, `localLR`, `localRR` are respectively
`choose L 2`, `L*R`, `choose R 2`. `local_pair_split` identifies their sum
with production `goldbachOffsetPrimePairMultiplicity` whenever the supports
are disjoint. The arithmetic dependence is in the disjointness hypothesis;
the combinatorial identity does not require primes.

`primitive_pair_split` sums the split over `primitiveParityOffsets`.
`full_pair_split` reconciles with the **existing full**
`goldbachPrimePairOverlapCount`: its value is the retained LL+LR+RR sum plus
the unchanged local pair multiplicities on removed offsets. Ignoring that
complement would not be an identity. This is a refinement of the ledger, not
an improvement of its capacity bound.

`higher_overlap_regression` kernel-checks the QP-002 scan minimum inside the
primitive-parity fiber: n=31,u=4, endpoints 27 and 35, left support {3}, right
support {5,7}, LL=0, LR=2, RR=1, production local Pascal residual=1. Thus even
a clean left/right separation leaves positive higher overlap. The finite
scan found the earlier primitive-without-parity example n=13,u=7, but its
shared two means LL+LR+RR does not describe the union pair count there.

The numerical script already computes and checks local LL/LR/RR in the
QP-002 snapshot, centers 0..500. No failures occurred on the normalized fiber.
This phase promotes the identity and its full-ledger reconciliation to
universal Lean proofs; the arithmetic structure of LR is audited next.

Validation: `lake build DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra`
from `lean/dk_math`, exit 0, 8692 jobs, scratch 7.3 seconds. The first attempt
at the full-sum proof timed out after rewriting the filtering set inside its
own predicate; an explicitly typed partition identity avoids that rewrite.
Final build has no scratch warnings. `git diff --check` passed.
