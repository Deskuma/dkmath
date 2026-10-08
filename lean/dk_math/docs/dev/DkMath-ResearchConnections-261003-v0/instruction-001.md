# DRC-001 — Finite-free lattice landing implementation instructions

Branch: **research/DkMath-ResearchConnections-261003-v0**

Base commit: **f16282e5b44bd5fe5afa1a15d29f1598cae575cd**

## Objective

Kernel-check the first genuinely new reusable theorem selected from the
2026-10-03 repository survey: the adjugate-coordinate criterion for integral
lattice landing.

The first implementation target is deliberately matrix-level.  Do not begin by
building a large finite-free algebra abstraction.

## 0. Preflight audit

Before writing code, inspect at least:

~~~text
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
DkMath/NumberTheory/GNDegreeFactorization.lean
DkMath/Lib.lean
~~~

and the pinned Mathlib matrix APIs for:

~~~text
Matrix.det
Matrix.adjugate
Matrix.mulVec
adjugate_mul / mul_adjugate identities
scalar matrices / diagonal matrices
coordinatewise integer divisibility
~~~

Use exact API names available in the pinned Lean/Mathlib version.  Do not
reimplement determinant or adjugate theory locally.

Also confirm again that

~~~lean
DkMath.NumberTheory.GN_mul_degree
~~~

already exists.  DRC-001 must not create another GN_ab theorem.

## 1. New production module

Preferred file:

~~~text
DkMath/Lib/NumberTheory/FiniteFreeLatticeLanding.lean
~~~

If the final theorem is purely matrix-theoretic, the namespace may be chosen to
reflect that, but keep the file in the neutral Lib/NumberTheory layer so later
TraceOne / cubic / cyclotomic wrappers can reuse it.

## 2. Core theorem

Aim for a theorem equivalent to the following shape, adapting syntax and names
to actual Mathlib APIs:

~~~lean
theorem exists_mulVec_eq_iff_adjugate_dvd
    {ι : Type _} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (v : ι → ℤ)
    (hdet : M.det ≠ 0) :
    (∃ w : ι → ℤ, M *ᵥ w = v) ↔
      ∀ i, M.det ∣ (M.adjugate *ᵥ v) i
~~~

A logically equivalent orientation is acceptable.

The important content is:

~~~text
v belongs to the integer image lattice of M

iff

every coordinate of adj(M) v is divisible by det(M).
~~~

Do not weaken the right side to a scalar norm condition.

## 3. Proof architecture

Forward direction:

~~~text
v = M w

adj(M) v
  = adj(M) M w
  = det(M) I w
  = det(M) w
~~~

so every coordinate is divisible by det(M).

Reverse direction:

~~~text
forall i, det(M) divides (adj(M) v)_i
~~~

Choose an integer vector w coordinatewise such that

~~~text
adj(M) v = det(M) * w.
~~~

Multiply by M:

~~~text
M adj(M) v = det(M) * M w.
~~~

Use the adjugate identity to rewrite the left side as

~~~text
det(M) * v.
~~~

Then cancel the nonzero integer det(M) coordinatewise and conclude

~~~text
v = M w.
~~~

Prefer standard algebraic cancellation lemmas over ad-hoc arithmetic.

## 4. Boundary discipline

The hypothesis

~~~text
M.det ≠ 0
~~~

is essential.

Do **not** replace it by merely saying that M is nonzero.  In a finite-free
algebra or cyclic group ring, a nonzero multiplication operator may still have
zero determinant.

Add at least one regression showing that the theorem is deliberately stated
only in the nonzero-determinant region.

## 5. Regressions

Add focused test coverage in DkMathTest, for example:

~~~text
DkMathTest/Lib/NumberTheory/FiniteFreeLatticeLandingCalibration.lean
DkMathTest/Lib/NumberTheory/FiniteFreeLatticeLandingAxiomAudit.lean
~~~

Exact paths may follow current test conventions.

Required checks:

1. a diagonal or triangular 2 x 2 integer matrix where the criterion is easy to
   verify;
2. a non-diagonal 2 x 2 matrix;
3. at least one vector failing one adjugate divisibility coordinate and hence
   failing image landing;
4. the public theorem's axiom audit.

If convenient, include the Gaussian-style conceptual calibration mentioned by
the survey: equal scalar norms alone need not imply divisibility.  This is
optional for DRC-001 because the core theorem itself is matrix-level.

## 6. Optional algebra wrapper

Only after the matrix theorem is green, investigate a wrapper for a
finite-free Z-algebra with a chosen basis.

Conceptually:

~~~text
beta : A
M_beta := matrix of multiplication by beta
v_alpha := coordinates of alpha

beta divides alpha
iff
all coordinates of adj(M_beta) v_alpha are divisible by det(M_beta)
~~~

This wrapper is **optional** in DRC-001.

Outcome A does not require it if Basis / LinearMap plumbing would dominate the
checkpoint.  In that case report the exact API boundary and leave the wrapper
for DRC-001B.

Do not assume that det(multiplication by beta) is already named or normalized
as the algebraic norm unless the exact Mathlib theorem is available and checked.

## 7. TraceOne compatibility

Do not rewrite TraceOneLatticeLanding during the first pass.

Instead, document whether its existing two-coordinate criterion is a concrete
rank-2 instance of the new matrix theorem.

A later refactor is allowed only if it:

- reduces duplicated proof;
- preserves theorem names or supplies compatibility wrappers;
- does not introduce heavier imports into the existing TraceOne path.

## 8. DkMath.Lib promotion

When the new module is stable:

- add the appropriate import to `DkMath/Lib.lean`;
- ensure the aggregate Lib import remains free of `sorry`, `admit`, and new
  axioms;
- avoid pulling unrelated research modules into the Lib closure.

## 9. Validation

Run at minimum:

~~~text
lake env lean DkMath/Lib/NumberTheory/FiniteFreeLatticeLanding.lean
lake env lean <new focused calibration test>
lake env lean <new axiom audit>
lake build DkMath.Lib
~~~

Then run the normal repository-wide build used by the project if resources
permit.

For the public theorem(s), record:

~~~lean
#print axioms <theorem-name>
~~~

Expected dependency profile should contain no `sorryAx` and no project-added
axioms.  Standard dependencies such as `propext`, `Classical.choice`, and
`Quot.sound` are acceptable when inherited from Mathlib.

## 10. Deliverable

Write:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-001.md
~~~

The report must contain:

- Outcome A / B / C;
- exact theorem names and files;
- proof architecture actually used;
- whether the algebra wrapper was implemented or deferred;
- relationship to TraceOneLatticeLanding;
- focused/full build results;
- axiom audit;
- any Mathlib API limitation encountered;
- no claim that the theorem is mathematically novel unless separately
  established.

Outcome meanings:

~~~text
A:
  matrix theorem kernel-checked with regressions and axiom audit.

B:
  a correct weaker/general intermediate theorem is fixed, but the exact
  iff target remains blocked by a concrete API/proof issue.

C:
  target cannot be implemented under the proposed assumptions; provide a
  counterexample or exact obstruction and revise the roadmap.
~~~

## 11. Hard stop rules

Do not use:

~~~text
sorry
admit
axiom
unsafe proof shortcuts
finite brute-force enumeration as replacement for proof
norm equality as replacement for coordinate divisibility
~~~

If a stronger theorem already exists in Mathlib or DkMath, stop duplicating and
report the existing theorem instead.
