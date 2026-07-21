# Instructions

## JAC-005

Implement checkpoint JAC-005 Rational Counterexample Certificate for the
DkMath Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian
- JAC-004 Determinant certificate

Stop after JAC-005.
Do not begin the complex lift or determinant-one normalization.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Collision
import DkMath.Hackathon.JacobianCounterexample3.Determinant
```

Add only immediately required Mathlib imports if the existing imports do not
already expose the needed function lemmas.

## Required theorem 1: noninjectivity

Prove:

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ := by
  ...
```

Preferred proof:

```lean
intro hinj
apply p0Q_ne_p1Q
apply hinj
rw [eval_p0Q, eval_p1Q]
```

Equivalent short proofs are acceptable.

The proof must use the actual evaluated polynomial map
`evalCounterexampleQ`; do not introduce a separate handwritten map.

## Required theorem 2: no left inverse

Prove:

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ := by
  ...
```

Preferred route:

```lean
rintro ⟨G, hG⟩
exact evalCounterexampleQ_notInjective hG.injective
```

If implicit type inference accepts the shorter existential binder, that is
also acceptable, but keep the public statement easy to read.

## Required theorem 3: compact rational certificate

Prove a compact theorem combining the local and global certificates.

Preferred statement:

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ := by
  exact ⟨
    jacobianMatrixQ_det_eq_neg_two,
    jacobianMatrixQ_det_ne_zero,
    evalCounterexampleQ_notInjective
  ⟩
```

This statement should keep the nonzero fact attached to the actual determinant,
rather than repeating only `(-2 : ℚ) ≠ 0`.

## Optional compact three-point certificate

The existing theorem:

```lean
three_point_collision_Q
```

already stores all three pairwise inequalities and all three image equalities.

Do not duplicate it.

It may be referenced in documentation or theorem comments, but the
noninjectivity proof should remain minimal and may use only `p0Q` and `p1Q`.

## Recommended theorem comments

Use comments that distinguish:

- explicit global collision;
- failure of injectivity;
- absence of a left inverse;
- constant nonzero formal Jacobian determinant.

Do not claim a complex Jacobian-conjecture counterexample yet. At JAC-005 the
coefficient and point world is still explicitly `ℚ`.

A suitable description is:

```text
A rational polynomial map with constant nonzero formal Jacobian determinant
and an explicit collision.
```

## Restrictions

Do not:

- alter the polynomial definitions;
- alter the collision points;
- recompute the determinant;
- introduce a second Jacobian;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin `ComplexLift.lean`;
- begin determinant-one normalization;
- begin Book of Magic general APIs;
- claim completion over `ℂ`.

## Optional aggregator

Do not create a top-level aggregator module unless it is required by the
current repository import convention.

If an aggregator is added, keep it limited to:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
```

but prefer to leave public-surface work for the later Demo checkpoint.

## Verification

Build:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
DkMath.Hackathon.JacobianCounterexample3.Counterexample
```

Temporary checks:

```lean
#check evalCounterexampleQ_notInjective
#check evalCounterexampleQ_noLeftInverse
#check jacobianCounterexampleCertificateQ
```

Remove temporary checks after verification.

Also run:

```text
git diff --check
```

## Report

Report:

1. exact imports;
2. exact theorem statements;
3. proof route for noninjectivity;
4. proof route for no left inverse;
5. exact structure of `jacobianCounterexampleCertificateQ`;
6. build result and warnings;
7. `git diff --check` result;
8. confirmation that JAC-006 and later checkpoints were not started.

Stop after JAC-005 and wait for review.
