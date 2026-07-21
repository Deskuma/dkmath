# Instructions

## JAC-004

Implement checkpoint JAC-004 Determinant Certificate for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian

Stop after JAC-004.
Do not implement the final counterexample certificate yet.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

Remove any redundant import only if this is immediate.
Do not spend checkpoint time on import minimization.

## Required theorem 1

Prove the exact polynomial identity:

```lean
theorem jacobianMatrixQ_det_eq_neg_two :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) := by
  ...
```

The proof must use the formal Jacobian already constructed through
`MvPolynomial.pderiv`.

Preferred route:

```lean
rw [jacobianMatrixQ_eq_explicit]
rw [Matrix.det_fin_three]
simp [explicitJacobianQ]
ring
```

Equivalent variants are allowed:

```lean
rw [jacobianMatrixQ_eq_explicit]
simp [Matrix.det_fin_three, explicitJacobianQ]
ring_nf
```

The current Mathlib theorem has the form:

```lean
Matrix.det_fin_three
    (A : Matrix (Fin 3) (Fin 3) R)
```

and expands the determinant into the standard six signed products.

If `rw [Matrix.det_fin_three]` does not match directly, use:

```lean
simp only [Matrix.det_fin_three]
```

or:

```lean
change explicitJacobianQ.det = MvPolynomial.C (-2 : ℚ)
rw [Matrix.det_fin_three]
```

after rewriting with `jacobianMatrixQ_eq_explicit`.

## Required theorem 2

Prove nonvanishing:

```lean
theorem jacobianMatrixQ_det_ne_zero :
    jacobianMatrixQ.det ≠ 0 := by
  rw [jacobianMatrixQ_det_eq_neg_two]
  norm_num
```

If `norm_num` does not close the `MvPolynomial.C` goal directly, use
the injectivity/nonzero simp API for `MvPolynomial.C`, for example:

```lean
rw [jacobianMatrixQ_det_eq_neg_two]
simp
```

or derive it from:

```lean
show (-2 : ℚ) ≠ 0 by norm_num
```

through the existing `MvPolynomial.C` simp lemmas.

## Proof-source requirements

The proof chain must remain:

```text
counterexamplePoly
  ↓ pderiv
jacobianMatrixQ
  ↓ jacobianMatrixQ_eq_explicit
explicitJacobianQ
  ↓ Matrix.det_fin_three
six-term determinant
  ↓ ring / ring_nf
C (-2)
```

Do not define a second determinant or a hand-written scalar expression as
the primary source of truth.

## Restrictions

Do not:

- modify the polynomial map unless a genuine error is found;
- redefine the Jacobian as the explicit matrix;
- assume the determinant value;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- implement `evalCounterexampleQ_notInjective`;
- implement the final conjunction certificate;
- implement the complex lift;
- implement determinant-one normalization;
- begin Book of Magic general APIs.

Ordinary kernel-checked tactics such as:

```text
simp
ring
ring_nf
norm_num
```

are allowed.

## Performance fallback

If expanding the determinant directly causes a large tactic state:

1. rewrite to `explicitJacobianQ`;
2. expand only with `Matrix.det_fin_three`;
3. simplify matrix indexing with `simp [explicitJacobianQ]`;
4. use `ring_nf`.

Do not split the determinant into an axiom or external certificate.

A private helper theorem for the determinant of `explicitJacobianQ` is
allowed if technically useful:

```lean
private theorem explicitJacobianQ_det_eq_neg_two :
    explicitJacobianQ.det = MvPolynomial.C (-2 : ℚ) := by
  ...
```

Then derive the public theorem by rewriting with
`jacobianMatrixQ_eq_explicit`.

Prefer the direct public proof if it remains readable.

## Verification

Build:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
```

Temporary checks may be used:

```lean
#check jacobianMatrixQ_det_eq_neg_two
#check jacobianMatrixQ_det_ne_zero
```

Remove them after verification unless placed intentionally in a later
Demo module.

## Report

Report:

1. exact imports;
2. exact theorem names;
3. the determinant expansion route used;
4. whether `Matrix.det_fin_three` rewrote directly;
5. whether `ring` or `ring_nf` closed the identity;
6. any performance or simplification friction;
7. build result and warnings;
8. `git diff --check` result;
9. confirmation that JAC-005 and later checkpoints were not started.

Stop after JAC-004 and wait for review.
