# IPSM-022 — Q1 integrability and ordering closeout roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: P2 Green / Q1 shifted-energy integrability open / no sign claim / no RH claim

## 0. Review

The current Q1 implementation is Green at the stated boundary:

- `ShiftedPlusEnergy` and `ShiftedMinusEnergy` are defined.
- each beam has an independent nonnegativity theorem;
- integrated polarization is proved under explicit `IntervalIntegrable` assumptions for the two shifted norm-square functions;
- under those assumptions, `MinusEnergy ≤ PlusEnergy` is equivalent to nonnegativity of the genuine complex vertical surface real part;
- the ordering gap is only an audit marker and does not claim impossibility.

The remaining issue is exactly the missing shifted norm-square integrability certificate. P2 rectangle `L¹` alone does not imply this `L²`-type statement.

## 1. Do not add a free integrability provider yet

There is a source-derived route available before introducing a provider:

```text
finite t-amplitude integrability
+ compact (t,u) kernel continuity
-> uniform kernel bound on [-T,T] x [-ε,ε]
-> dominated parameter integral
-> continuity of F_X(u) on [-ε,ε]
-> continuity of normSq(F_X(u) ± 1)
-> shifted IntervalIntegrable certificates
```

Here `F_X(u)` is `pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u`.

The Gamma/logDeriv term still does not need joint continuity: it remains inside the t-only integrable amplitude.

## 2. Q1-I1 — continuity of the aggregate on the finite u-window

Use the already separated box kernel

```lean
pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u
```

and amplitude

```lean
pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t.
```

Let

```text
K = uIcc(-T,T) ×ˢ uIcc(-ε,ε).
```

The kernel is already globally continuous. Since `K` is compact, obtain a constant `C` with

```text
‖BoxKernel W t u‖ ≤ C
```

for `(t,u) ∈ K`, using the compact continuous bound API (`IsCompact.exists_bound_of_continuousOn` or the pinned equivalent).

Use as t-dominating function

```text
bound(t) = C * ‖VerticalAmplitude W X t‖
```

on the restricted finite t-measure. Its integrability follows from

```lean
pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable
```

already proved in P2-A.

Then apply `MeasureTheory.continuousOn_of_dominated` to the parameterized t-integral on `u ∈ Icc (-ε) ε`.

Recommended helper endpoint:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X)
      (Set.Icc (-ε) ε) := by
  ...
```

If direct use of `intervalIntegral` blocks the dominated theorem, first define/prove continuity for the restricted set integral with measure

```lean
volume.restrict (Set.uIoc (-W.rectangle.T) W.rectangle.T)
```

and then rewrite it to the interval integral using `W.rectangle.hT : 0 < T`.

Do not use any `T → ∞`, `X → ∞`, or `ε → 0` argument.

## 3. Q1-I2 — shifted norm-square interval integrability

From aggregate continuity on `Icc (-ε) ε`, prove continuity on the same compact interval of

```lean
fun u => Complex.normSq (F_X u + 1)
```

and

```lean
fun u => Complex.normSq (F_X u - 1).
```

Then obtain finite-interval integrability using the compact/Icc integration API (`ContinuousOn.integrableOn_Icc` or the pinned equivalent), and convert to `IntervalIntegrable`.

Target public theorems:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationShiftedPlus_intervalIntegrable
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1))
      volume (-ε) ε := by
  ...

 theorem pascalCenteredXiPrimeSideQuadraticizationShiftedMinus_intervalIntegrable
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1))
      volume (-ε) ε := by
  ...
```

No positivity assumption on `ε` should be needed merely for integrability unless required by a helper theorem.

## 4. Q1-I3 — remove conditional hypotheses

Use the concrete certificates to close unconditional wrappers:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X : ℂ) -
      (pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X : ℂ) := by
  exact pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference_of_integrable
    hε W X
    (pascalCenteredXiPrimeSideQuadraticizationShiftedPlus_intervalIntegrable (ε := ε) W X)
    (pascalCenteredXiPrimeSideQuadraticizationShiftedMinus_intervalIntegrable (ε := ε) W X)
```

and

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X ↔
      0 ≤ (pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X).re := by
  ...
```

Keep the existing conditional theorems if useful as lower-level APIs.

## 5. Q1 ordering audit after integrability closes

Once the unconditional equivalence is Green, classify Q1 carefully:

```text
E+ ≥ 0                         GREEN
E- ≥ 0                         GREEN
4 V = E+ - E-                  GREEN
E- ≤ E+ ↔ Re(V) ≥ 0            GREEN
independent source ordering     OPEN
```

Thus PSD of the two shifted beams alone gives no order between them.

Do not introduce a structure whose essential field is merely

```lean
MinusEnergy ≤ PlusEnergy
```

and then call that an independent positivity provider. By the theorem above, such a field is exactly the vertical sign target in renamed form.

A future ordering theorem is meaningful only if derived from new source-level structure independent of the desired inequality.

If no such structure is found, close Q1 as a named equivalence/ordering obstruction and move to Q2/Q3 rather than repeatedly repackaging the same sign target.

## 6. Optional algebraic closeout

If convenient after integrability, prove the sum identity

```text
E+ + E- = 2 E0 + 2
```

with the exact normalization used in the file. Together with

```text
E+ - E- = 4 Re(V)
```

this gives the two-beam decomposition explicitly. This is structural only and supplies no sign.

## 7. Firewall

Keep unchanged:

```text
shifted-energy integrability != shifted-energy ordering
vertical ordering            != whole scalar-excess sign
whole scalar-excess sign     != RH
```

Top-horizontal and radial comparison remain outside the vertical shifted energies.

Do not use zero-side anti-mirror energy.
Do not absorb top-horizontal or radial terms by definition.
Do not exchange the established limit order.
No `X → ∞`, `ε → 0+`, or `T → ∞` argument belongs in this Q1 finite-window checkpoint.
