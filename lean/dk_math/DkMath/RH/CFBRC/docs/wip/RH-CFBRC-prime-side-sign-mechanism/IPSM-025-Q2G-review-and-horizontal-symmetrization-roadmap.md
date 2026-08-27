# IPSM-025 — Q2-G review and horizontal symmetrization roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

## 0. Review result

IPSM-024 and Q2-G are Green.

Verified theorem surface:

```text
safe-half-plane completed-zeta conjugation     GREEN
fixed Xi kernel global conjugation              GREEN
centered kernel conjugation                     GREEN
derivative / totalized logDeriv conjugation     GREEN
TopAmplitude(1-x) = -conj(TopAmplitude(x))       GREEN
TopBoxFeature(1-x,v) = -conj(TopBoxFeature(x,-v)) GREEN
```

The former `HorizontalConjugationGap` may remain deleted.

No sign, whole ordering, radial comparison, limit exchange, or RH claim follows from this closeout.

## 1. Q2-H1 — aggregate reflection

Let the existing top aggregate be abbreviated by `A(v)`.

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_neg_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W (-v) =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v) := by
  ...
```

Use the already Green pointwise theorem with `v := -v` and the same affine substitution used in the horizontal-pairing module:

```lean
intervalIntegral.integral_comp_sub_left
```

The oriented interval `W.rectangle.σ .. 1 - W.rectangle.σ` is invariant under `x ↦ 1-x` in exactly the sense already used by `pascalCenteredXiBottomHorizontalContribution_eq_top`.

Move conjugation through the interval integral with the pinned interval-conjugation API already used by the vertical aggregate proof.

Do not replace this by an orientation-free informal symmetry argument.

## 2. Q2-H2 — horizontal deoriented aggregate

Define the feature carrying the actual whole-surface orientation:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  -Complex.I *
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v
```

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v) := by
  ...
```

This is the key conversion:

```text
raw top aggregate:         A(-v) = -conj(A(v))
deoriented aggregate:      H(-v) =  conj(H(v))
```

Do not claim `H(v) = conj(H(v))` pointwise.

## 3. Q2-H3 — continuity on a finite box interval

To split and symmetrize interval integrals cleanly, prove continuity of the top aggregate on every finite box interval.

Repeat the already Green vertical dominated-parameter argument:

```text
TopAmplitude finite-interval L1
+ compact bound for TopBoxKernel
+ continuous kernel in v
-> ContinuousOn TopAggregatedBoxFeature on uIcc(-ε, ε)
```

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_continuousOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W)
      (Set.uIcc (-ε) ε) := by
  ...
```

Then obtain `IntervalIntegrable` wrappers for the raw and deoriented horizontal aggregates as needed.

Do not introduce a free integrability provider unless the concrete dominated route fails for a precise Mathlib reason.

## 4. Q2-I1 — real symmetrized horizontal feature

Define:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v)) / 2
```

Prove both:

```lean
pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature_neg
pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature_eq_conj
```

Expected content:

```text
S(-v) = S(v)
S(v)  = conj(S(v))
```

The second theorem is the pointwise reality certificate needed by the whole-feature layer.

## 5. Q2-I2 — symmetrization preserves the actual horizontal source

Use the symmetric box interval and `intervalIntegral.integral_comp_neg` to prove that averaging `H(-v)` gives the same result as averaging `H(v)`.

Then prove:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_horizontalSymmetricFeature_average_eq_deorientedHorizontalBase
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v =
      -Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W := by
  ...
```

Load-bearing input:

```lean
pascalCenteredXiPrimeSideQuadraticization_horizontalBase_eq_normalized_topAggregate
```

This theorem must show that symmetrization preserves the existing horizontal source. It must not redefine `HorizontalBase`.

## 6. Q2-J1 — whole finite feature

Define:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v
```

The vertical aggregate is already pointwise real. Combine it with Q2-I1 to prove:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) := by
  ...
```

Also prove finite-interval continuity / integrability by adding the already available vertical and horizontal certificates.

## 7. Q2-J2 — exact whole-surface box-average identity

Target:

```lean
theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v := by
  ...
```

Use only the already Green identities:

```text
ComplexVerticalSurface = normalized average of vertical aggregate
-I * HorizontalBase    = normalized average of horizontal symmetric feature
ComplexWholeSurface    = ComplexVerticalSurface - I * HorizontalBase
```

No radial term belongs in this theorem.

## 8. Q2-J3 — whole finite surface is real

Once Q2-J2 and pointwise whole-feature reality are Green, prove:

```lean
theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_conj ...
```

and then, using the existing theorem

```lean
pascalCenteredXiMellinQuadraticComplexWholeSurface_re_eq_scalarSurface
```

obtain the stronger cast identity if convenient:

```lean
theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_scalarSurface
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      (pascalCenteredXiMellinQuadraticScalarSurface ε W X : ℂ) := by
  ...
```

This is a reality/source-representation theorem, not a positivity theorem.

## 9. Q2 closeout boundary

If Q2-J closes, classify the state as:

```text
vertical real feature                       GREEN
horizontal source-derived real feature      GREEN
whole finite real feature                   GREEN
whole finite source box-average identity    GREEN
whole finite surface reality                GREEN
whole sign                                  OPEN
radial comparison                           OPEN
```

Only after this should whole shifted-energy polarization be introduced.

## 10. Next gate after this file

The next checkpoint should be Q2-K:

```text
whole feature continuity
-> whole shifted +1/-1 energies
-> independent nonnegativity
-> exact whole polarization
-> whole ordering iff ScalarSurface >= 0
```

As in Q1, do not interpret two PSD beams as an ordering theorem.

If whole ordering has no independent source provider, close Q2 with a named ordering gap and proceed to Q3 radial comparison.

## 11. Firewall

```text
whole source reality
!= whole source nonnegativity

whole source nonnegativity
!= scalar excess nonnegativity

scalar excess nonnegativity
!= RH without the established ordered limit bridge
```

Keep the radial subtraction outside Q2.

Do not use the zero-side anti-mirror energy to order the whole shifted energies.

Do not introduce `T -> infinity`, `ε -> 0`, or any limit exchange in this finite-feature layer.
