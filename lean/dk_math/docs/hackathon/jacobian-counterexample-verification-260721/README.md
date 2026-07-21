# Jacobian Counterexample Verification

## Status

JAC-001 through JAC-011 are complete. DkMath now exposes a Lean 4 + Mathlib
certificate for the stated three-dimensional polynomial formulas, their
constant Jacobian determinant, and their explicit collision.

## Verified map

For `(x,y,z) ∈ ℂ³`, the project verifies the polynomial map `F = (P,Q,R)`:

```text
P = (1 + xy)^3 z + y^2 (1 + xy) (4 + 3xy)
Q = y + 3x (1 + xy)^2 z + 3xy^2 (4 + 3xy)
R = 2x - 3x^2y - x^3z
```

Its formal Jacobian is generated from these polynomials with
`MvPolynomial.pderiv`; Lean proves its determinant is the constant `-2`.

## Normalized map

The presentation map multiplies the first output coordinate by `-1/2`:

```text
F̃ = (-P/2, Q, R).
```

Consequently its formal Jacobian determinant is `1`. The original common
target is `(-1/4, 0, 0)`; applying `normalizeOutputC targetC` gives the
normalized common target exactly `(1/8, 0, 0)`.

## Main Lean certificates

```text
jacobianCounterexampleCertificateQ
jacobianCounterexampleCertificateC
normalizedJacobianCounterexampleCertificateC
jacobianDemoCertificateC
normalized_three_point_collision_C
evalNormalizedCounterexampleC_noLeftInverse
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
eval_add_sub_eval_eq_mul_GNFiniteDifference
differenceQuotient_eq_GNFiniteDifference
```

## Three-point collision

The three pairwise distinct inputs

```text
(0, 0, -1/4)
(1, -3/2, 13/2)
(-1, 3/2, 13/2)
```

all map under `F̃` to `(1/8, 0, 0)`. Hence `F̃` is not injective and has no
set-theoretic left inverse.

## Module map

```text
DkMath/Hackathon/JacobianCounterexample3/
├── Basic.lean
├── PolynomialMap.lean
├── Collision.lean
├── Jacobian.lean
├── Determinant.lean
├── Counterexample.lean
├── ComplexLift.lean
├── Normalized.lean
├── GapCrystalBridge.lean
└── Demo.lean

DkMath/Hackathon/JacobianCounterexample3.lean

DkMath/BookOfMagic/
├── UniqueGapContract.lean
├── GapCrystal.lean
└── GNFiniteDifference.lean

DkMath/BookOfMagic.lean
```

## Build

Run from `lean/dk_math`:

```sh
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMath.BookOfMagic
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMath
```

The root build may report unrelated pre-existing warnings outside this project.

## Axiom audit

`DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms` audits the rational,
complex, normalized, and Demo summit certificates. The accepted foundations are
the standard Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`;
the audit must contain neither `sorryAx` nor a DkMath-specific axiom.

This is a Lean kernel-checked algebraic certificate. Historical priority,
authorship, publication status, and external review are separate questions and
are not certified by Lean.

## Book of Magic interpretation

The normalized output is treated as a Core and its restoring inputs as Gaps.
The collision yields failure of `UniqueGap` and noninjectivity of `forgetGap`.
`GapCrystal` packages a valid Core–Gap pair. This is a DkMath interpretation
layer added after the counterexample certificate.

## GN finite-difference recovery

`GNFiniteDifference` proves for a general polynomial that evaluation at `t+h`
minus evaluation at `t` factors by `h`, and identifies the difference quotient
when `h ≠ 0`. This generic Book of Magic theorem is independent of the
Jacobian certificate.

## Scope and non-goals

This project independently formalizes and verifies the displayed formulas. It
does not claim that DkMath discovered them, settle the two-dimensional case,
formalize the general Jacobian conjecture, reconstruct a search procedure, or
provide historical or peer-review certification. Higher-dimensional padding
and `PrincipalPartCompletion` are deferred.

## Provenance

The repository record credits a public post by Levent Alpöge and supplies its
URL. Exact field-by-field source status and the distinction between the source,
DkMath verification, and DkMath interpretation are recorded in
[`PROVENANCE.md`](PROVENANCE.md).
