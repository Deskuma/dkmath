# IPSM-026 — Q2-K whole shifted-energy polarization and ordering audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q2-J Green / Q2-K whole shifted-energy closeout / radial comparison remains Q3 / no sign or RH claim

## 0. Q2-J review

The current source implementation is Green through Q2-J.

The module now proves:

```text
TopAggregate(-v) = -conj(TopAggregate(v))              GREEN
HorizontalDeorientedAggregate(-v) = conj(...)           GREEN
HorizontalSymmetricFeature is pointwise real            GREEN
average(HorizontalSymmetricFeature) = -I * HorizontalBase GREEN
WholeBoxFeature is pointwise real                        GREEN
WholeBoxFeature is ContinuousOn every finite box         GREEN
WholeBoxFeature is IntervalIntegrable                     GREEN
ComplexWholeSurface = normalized average WholeBoxFeature  GREEN
ComplexWholeSurface = conj(ComplexWholeSurface)           GREEN
ComplexWholeSurface = (ScalarSurface : ℂ)                 GREEN
```

This is a genuine source-level finite whole-feature representation. The horizontal source was not absorbed by definition; it was transported through the actual top-edge box source, deorientation and source-derived symmetrization.

## 1. Q2-K objective

Repeat the Q1 polarization layer on the **whole finite pointwise-real feature**.

This should close:

```text
WholeE+ >= 0                                     GREEN target
WholeE- >= 0                                     GREEN target
4 * ScalarSurface = WholeE+ - WholeE-            GREEN target
WholeE- <= WholeE+ iff 0 <= ScalarSurface         GREEN target
independent whole ordering provider               audit target
```

This does not include the radial subtraction.

## 2. Q2-K1 — whole shifted energies

Define:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ v in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1)

noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ v in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1)
```

Keep these distinct from the earlier vertical-only `ShiftedPlusEnergy` / `ShiftedMinusEnergy`.

## 3. Q2-K2 — unconditional shifted integrability

No free integrability provider is needed.

From:

```lean
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_continuousOn
```

obtain unconditional theorems:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1))
      volume (-ε) ε := by
  ...

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1))
      volume (-ε) ε := by
  ...
```

Use the same `Complex.continuous_normSq` pattern already used for Q1.

## 4. Q2-K3 — independent PSD of both whole beams

For `hε : 0 < ε`, prove independently:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy_nonneg ... :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X := by
  ...

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy_nonneg ... :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X := by
  ...
```

The proof should use only:

```text
0 <= (2ε)^-1
normSq >= 0
finite symmetric interval orientation from hε
```

Do not derive one beam's nonnegativity from the other.

## 5. Q2-K4 — pointwise whole polarization

Reuse the already proved generic theorem:

```lean
pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
```

with:

```lean
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_eq_conj
```

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_polarization_pointwise
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) :
    (4 : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v =
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ) -
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ) := by
  ...
```

No new algebra should be invented here.

## 6. Q2-K5 — integrated whole polarization

Use:

```lean
pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
```

plus the unconditional shifted integrability theorems.

Target the complex identity first:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X : ℂ) := by
  ...
```

The Q1 proof may be copied structurally, replacing the vertical feature by `WholeBoxFeature` and using its already concrete integrability.

Then derive the real scalar theorem using the already Green identity:

```lean
pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_scalarSurface
```

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    4 * pascalCenteredXiMellinQuadraticScalarSurface ε W X =
      pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X -
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X := by
  ...
```

This scalar form is the preferred theorem for the ordering audit.

## 7. Q2-K6 — ordering equivalence

Prove directly:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_wholeShiftedEnergy_order_iff_scalarSurface_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X ↔
      0 ≤ pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  ...
```

This is expected to be a short `linarith` consequence of the scalar difference identity.

Do not misclassify this equivalence as a sign theorem.

## 8. Q2-K7 — whole ordering gap

Search for an **independent source theorem** that orders the two whole shifted energies.

The following do not count as independent ordering providers:

```text
- rewriting with the scalar-surface difference identity
- assuming `0 <= ScalarSurface`
- using the ordering equivalence backwards
- using positivity of the individual energies alone
- importing the radial defect / zero-side anti-mirror energy
```

If no independent provider exists, add a distinct marker:

```lean
inductive PascalCenteredXiPrimeSideQuadraticizationWholeShiftedEnergyOrderingGap : Prop
  | noIndependentWholeOrderingProvider :
      PascalCenteredXiPrimeSideQuadraticizationWholeShiftedEnergyOrderingGap
```

Do not reuse the vertical-only gap marker as if the observables were identical.

## 9. Optional useful identities

If they are cheap, prove the whole analogues of the energy-sum decomposition.

For a pointwise-real `F`:

```text
|F+1|² + |F-1|² = 2|F|² + 2.
```

After normalized integration on `[-ε, ε]`, the constant contribution is exactly `2`, because the normalized interval mass is `1` for `ε > 0`.

This gives the useful coordinate system:

```text
WholeE+ - WholeE- = 4 * ScalarSurface
WholeE+ + WholeE- = 2 * WholeE0 + 2
```

and therefore formally:

```text
WholeE+ = WholeE0 + 1 + 2 * ScalarSurface
WholeE- = WholeE0 + 1 - 2 * ScalarSurface
```

These identities are optional. They clarify that ordering information remains exactly the sign coordinate.

## 10. Critical firewall: scalar surface versus scalar excess

Q2-K ends at the finite scalar surface.

Keep explicit:

```text
ScalarSurface
!= ScalarExcess
```

The existing definition is:

```text
ScalarExcess = ScalarSurface - π * FixedRadialSecondMomentFunctional(R).
```

Therefore even a hypothetical proof

```text
0 <= ScalarSurface
```

would **not** establish

```text
0 <= ScalarExcess.
```

The radial comparison is the entire content of Q3.

Do not insert the radial mass into `WholeShiftedPlusEnergy` or `WholeShiftedMinusEnergy` merely to manufacture a completion of square.

## 11. Q2-K acceptance checklist

```text
[ ] WholeShiftedPlusEnergy defined separately from vertical energy
[ ] WholeShiftedMinusEnergy defined separately from vertical energy
[ ] shifted norm-square integrability is unconditional and source-derived
[ ] WholeE+ nonnegative independently
[ ] WholeE- nonnegative independently
[ ] pointwise polarization reuses WholeBoxFeature reality
[ ] complex whole-surface difference identity compiled
[ ] scalar-surface difference identity compiled
[ ] WholeE- <= WholeE+ iff 0 <= ScalarSurface compiled
[ ] independent whole ordering provider audited
[ ] named whole-ordering gap added if absent
[ ] radial term remains outside both whole shifted energies
[ ] ScalarSurface is not confused with ScalarExcess
[ ] no X -> infinity argument
[ ] no ε -> 0 argument
[ ] no T -> infinity argument
[ ] no limit exchange
[ ] no RH consequence
```

## 12. Expected Q2 closeout

If the expected obstruction persists, close Q2 as:

```text
vertical source quadraticization                    GREEN
horizontal source quadraticization                  GREEN
whole finite real feature                           GREEN
whole shifted energies PSD                          GREEN
whole exact polarization                            GREEN
whole ordering <-> scalar-surface sign              GREEN
independent whole ordering                          OPEN
radial comparison                                   NEXT Q3
```

This is a strong and clean Q2 closeout: the entire finite arithmetic contour surface has been moved into one pointwise-real source-derived feature space, and its sign is exactly represented by ordering of two PSD beams. The remaining sign obstruction is no longer hidden inside contour orientation or complex phases.
