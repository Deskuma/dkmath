# DRC-002 — GN product-degree generic lift

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Determine whether the existing Nat theorem

~~~lean
DkMath.NumberTheory.GN_mul_degree
~~~

has a genuinely more general cancellation-free form over the natural generic
coefficient class used by GN.

The desired mathematical result is the product-degree identity

~~~text
GN (a * b) x u
  = GN a x u * GN b (x * GN a x u) (u ^ a)
~~~

without requiring a positive/nonzero gap merely to cancel x.

In particular, the generic statement should include the boundary x = 0 when
the algebraic assumptions make the identity meaningful.

## What to do

Treat this as an audit-and-formalize task.

1. Search DkMath and the pinned Mathlib for an existing theorem that already
   gives this identity at the desired level of generality.
2. If an adequate theorem already exists, do not duplicate it. Record the
   result and make only useful API/facade/calibration changes.
3. If it does not exist, formulate and kernel-check the strongest clean
   reusable version that the existing GN definition supports.
4. Reuse existing Cosmic Formula / GTail / GN infrastructure rather than
   creating a parallel definition.
5. Keep the existing Nat theorem working. Refactor it only if the generic
   theorem gives a clearly better and stable implementation path.

The exact theorem name, proof strategy, imports, and weakest practical typeclass
assumptions are for you to determine from the repository and pinned APIs.

## Expected outcome

A successful Outcome A should leave DkMath with a production theorem expressing
the cancellation-free product-degree composition of GN, including the zero-gap
boundary, together with focused regression coverage and an axiom audit.

The result should make clear that the already-existing Nat theorem is a
specialized consequence or compatibility theorem, not a separately rediscovered
fact.

## Boundaries

Do not:

- add a duplicate of `GN_mul_degree`;
- prove the result by assuming x is cancellable if a cancellation-free
  polynomial/finite-sum identity is available;
- strengthen assumptions merely to make the proof easier without reporting why;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty from this repository generalization alone.

If the proposed generic statement is false or the existing GN abstraction
cannot support it under the intended assumptions, produce the sharpest correct
result and explain the obstruction.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- relevant regressions;
- `DkMath.Lib` integration if the theorem belongs there;
- full build when practical;
- `#print axioms` for new public endpoints.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-002.md
~~~

with Outcome A / B / C, the exact result obtained, what was already present,
what was added, validation results, and any obstruction or design decision.

Do not finish the checkpoint without a report, even if the desired theorem
cannot be completed.
