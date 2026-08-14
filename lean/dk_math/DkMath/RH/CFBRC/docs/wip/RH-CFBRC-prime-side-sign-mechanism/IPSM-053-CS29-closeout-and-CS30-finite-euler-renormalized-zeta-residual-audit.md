# IPSM-053 — CS29 closeout and CS30 finite Euler-renormalized zeta residual audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS29 verdict: **Green-B**.

CS29 has now proved, entirely at finite `ε`, finite residue window `W`, and finite arithmetic cutoff `X`:

- `Re (((2πi)⁻¹) Z) = Im Z / (2π)`,
- the scalar projection of the finite top zeta-cutoff mismatch,
- conjugation of the phase, mode, and aggregate finite potentials,
- conjugation relations among the centered rectangle corners,
- exact four-edge telescoping of the finite arithmetic potential companions,
- `BottomCompanion = -conj TopCompanion`,
- finite FTC for the right companion,
- `RightCompanion = 2 i · AggregateInteraction`,
- normalized right companion `= AggregateInteraction / π`,
- the normalized scalar form of the CS28 top ledger,
- and counterexamples showing that controlling the surviving scalar component is strictly weaker than controlling the whole complex mismatch.

No independent scalar mismatch estimate, infinite series exchange, limit exchange, endpoint sign, or RH conclusion has been introduced.

## 1. First correction: the scalar mismatch is not automatically an error-to-zero target

Do **not** promote

```text
FiniteTopZetaMismatchScalar → 0
```

as the next desired provider merely because the object is called a mismatch.

The CS23 complete finite source contains the normalized top contribution with a **positive** sign, and CS29 decomposes that top contribution into:

```text
finite arithmetic top companion
+ top archimedean companion
+ top elementary companion
+ scalar zeta-cutoff mismatch.
```

Since the radial-contact deficit has the orientation

```text
G = π · (Q_R - completeSource),
```

increasing the scalar mismatch lowers `G`. Therefore the relevant target is a **lower reach condition relative to the remaining finite rectangle background**, not necessarily smallness of the mismatch itself.

CS30 must make this sign direction exact before any analytic estimate is attempted.

## 2. CS30-A — normalized finite complement boundary scalar

Define the normalized scalar of the two finite potential edges not used in the right+top source presentation:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteComplementBoundaryScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    (pascalCenteredXiPrimeSideFiniteLeftCompanion ε W X +
     pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X)).re
```

Use the CS29 four-edge telescope together with

```text
normalized RightCompanion = AggregateInteraction / π
```

and the CS25/CS24 prime normalization to prove the exact scalar identity

```text
NormalizedPrimeContribution
+ FiniteTopArithmeticCompanionScalar
= -FiniteComplementBoundaryScalar.
```

This theorem is purely finite and algebraic.

## 3. CS30-B — finite rectangle background

Define the scalar background left after the finite arithmetic right+top companions are removed by the rectangle telescope.

A canonical choice is

```text
B_{ε,W,X}
  := Q_R
   + FiniteComplementBoundaryScalar(ε,W,X)
   - NormalizedRightArchimedeanContribution(ε,W)
   - NormalizedRightElementaryContribution(ε,W)
   - 2 · FiniteTopArchimedeanCompanionScalar(ε,W)
   - 2 · FiniteTopElementaryCompanionScalar(ε,W).
```

Use existing exact source identities only. Under the CS28 top factor-safety and the three finite top integrability hypotheses, prove

```text
G(ε,W,X)
  = π · (B_{ε,W,X} - FiniteTopZetaMismatchScalar(ε,W,X)).
```

Check all factors of `2` against the existing definitions:

- right archimedean / elementary normalized contributions already contain the factor `2` from the finite explicit formula,
- `FiniteTopArchimedeanCompanionScalar` and `FiniteTopElementaryCompanionScalar` are normalized from a single top contribution, while the CS28/CS29 top ledger contains `2 * topContribution`.

Do not simplify factors by inspection; let Lean fix the coefficients.

## 4. CS30-C — exact mismatch reach classification

From `π > 0`, prove for arbitrary real tolerance `η`:

```text
G(ε,W,X) ≤ η
↔
B_{ε,W,X} - η / π
  ≤ FiniteTopZetaMismatchScalar(ε,W,X).
```

In particular:

```text
G(ε,W,X) ≤ 0
↔
B_{ε,W,X}
  ≤ FiniteTopZetaMismatchScalar(ε,W,X).
```

This is a **strength classification**, not a provider.

It prevents a later proof from accidentally treating mismatch smallness as the desired sign direction.

If a pure-real countermodel is useful, add one showing that `MismatchScalar = 0` need not imply contact when the background is positive, and that a large positive mismatch can produce contact.

## 5. CS30-D — finite prime-power Euler log potential

Return to the finite prime-power pair support from `PascalPrimePowerCanonicalFold`.

For `pk = (p,k)` in `pascalPrimePowerPairSupportUpTo X`, the actual exponent is `j = k + 1`.

Define a **finite Euler log potential**

```text
A_X(s)
  := Σ_{(p,k) in pairSupport(X)}
       (1 / (k+1)) · eulerPrimePowerMode(p,k+1,s).
```

Use a coefficient type convenient for complex differentiation, but retain the exact mathematical coefficient `1/(k+1)`.

Do not use an infinite Euler product or an infinite logarithmic expansion.

Prove termwise and then by the finite sum:

```text
A_X'(s) = - pascalPrimePowerPHZFiniteUpTo X s.
```

The key arithmetic cancellation is

```text
(1/j) · d/ds[p^{-js}]
  = -log(p) · p^{-js},
```

which matches the existing pair-support PHZ coefficient.

Prefer reusing:

- `pascalPrimePowerPairSupportUpTo`,
- `pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum`,
- `eulerPrimePowerMode_eq_primePower_cpow_neg`,

rather than rebuilding prime-power uniqueness.

## 6. CS30-E — finite Euler compensator and renormalized zeta residual

Define

```text
EulerCompensator_X(s) := exp(-A_X(s))
```

and

```text
EulerRenormalizedZetaResidual_X(s)
  := riemannZeta(s) * EulerCompensator_X(s).
```

The compensator is entire and nonzero because it is an exponential of a finite holomorphic sum.

Prove

```text
logDeriv(EulerCompensator_X)(s)
  = pascalPrimePowerPHZFiniteUpTo X s.
```

Then, at a point with the ordinary local zeta hypotheses needed by the repository (`s ≠ 1`, `riemannZeta s ≠ 0`; include any additional differentiability hypothesis only if Mathlib actually requires it), prove

```text
-logDeriv(EulerRenormalizedZetaResidual_X)(s)
  = pascalXiOrdinaryZetaNegLogDeriv(s)
    - pascalPrimePowerPHZFiniteUpTo X s.
```

This sign is critical.

The residual factor uses `exp(-A_X)`, not `exp(A_X)`.

With `A_X' = -PHZ_X`, one has

```text
logDeriv(exp(-A_X)) = +PHZ_X,
```

so the negative log derivative of `ζ · exp(-A_X)` is exactly

```text
-ζ'/ζ - PHZ_X.
```

## 7. CS30-F — top mismatch as one residual log-derivative integral

Under the CS28 top factor-safety hypothesis, prove pointwise on the top edge:

```text
pascalXiOrdinaryZetaNegLogDeriv(s(u))
  - pascalPrimePowerPHZFiniteUpTo X (s(u))
=
-logDeriv(EulerRenormalizedZetaResidual_X)(s(u)).
```

Then rewrite the finite complex mismatch exactly as

```text
TopZetaCutoffMismatch(ε,W,X)
  = 2 ∫_{σ}^{1-σ}
      h_ε(z(u)) ·
      (-logDeriv(EulerRenormalizedZetaResidual_X)(s(u))) du.
```

No infinite series appears in this theorem.

Also export the scalar projection:

```text
FiniteTopZetaMismatchScalar
  = Im(the residual-log-derivative integral) / π
```

with the exact normalization dictated by the existing factor `2`.

## 8. CS30-G — zero-free residual on the safe top edge

Under `IsPascalCenteredXiTopLogDerivDecompositionSafe W`, prove that

```text
EulerRenormalizedZetaResidual_X(s(u)) ≠ 0
```

for every top-edge point in the finite interval.

This follows from:

- `riemannZeta(s(u)) ≠ 0` from the explicit top safety contract,
- `exp(-A_X(s(u))) ≠ 0` unconditionally.

This theorem is important for future one-dimensional logarithm / phase-lift work, but CS30 must not assume a global complex logarithm branch that has not been constructed.

## 9. Optional CS30-H — finite residual normalization checks

Useful safe checks include:

- `X = 0` or `X = 1` gives `A_X = 0` and residual `= ζ`, if this follows from the existing support definitions.
- the compensator is never zero,
- no claim that the residual tends to `1` on the critical strip,
- no claim that the top mismatch tends to `0`.

The last two are explicit firewalls.

## 10. Research interpretation

CS29 showed that only one scalar component of the top mismatch survives the `(2πi)⁻¹` normalization.

CS30 should now show two further facts:

1. that this scalar is a **reach variable relative to a finite rectangle background**, not automatically an error-to-zero variable;
2. that the zeta-vs-PHZ difference is the negative logarithmic derivative of one finite Euler-renormalized zeta residual.

Thus the source progression becomes

```text
finite zeta / PHZ mismatch
→ finite prime-power log potential
→ Euler compensator
→ one zero-free renormalized residual factor
→ weighted residual log-derivative scalar.
```

This is a genuine source compression. It does not prove a sign.

## 11. Expected verdicts

### Green

In addition to the exact residual factorization, an independent source-derived estimate on the required scalar reach is proved without assuming radial contact, endpoint sign, fixed-defect nonnegativity, or RH.

### Green-B

The background/reach classification and the finite Euler-renormalized residual identities are proved exactly, but no independent scalar reach estimate is obtained.

### Yellow

The background classification closes, but the finite Euler log-potential derivative cannot be matched to the existing PHZ representation without a missing local complex-power derivative bridge. Record the exact missing theorem rather than introducing an assumption.

### Red

Any implementation that:

- assumes `FiniteTopZetaMismatchScalar → 0` as the desired conclusion,
- uses an infinite Euler product or infinite prime-series expansion on the top edge,
- exchanges an infinite limit with the top integral,
- assumes radial contact or the desired mismatch reach,
- imports the zero-side fixed-defect sign as a provider,
- or concludes RH.

## 12. Required gap marker

If no independent scalar reach estimate is proved, keep a narrow frontier such as

```lean
inductive PascalCenteredXiPrimeSideFiniteEulerResidualScalarReachGap : Prop
  | noIndependentFiniteEulerResidualScalarReachEstimate
```

Do not remove the CS29 scalar mismatch gap unless the new theorem genuinely discharges it.

## 13. Validation

Run at least:

```text
lake env lean <new-CS30-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.
