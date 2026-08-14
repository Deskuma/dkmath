# IPSM-019 — P0/P1/P3/P4 review and P2 rectangle-Fubini roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3 product/polarization review / P2 finite-rectangle exchange roadmap / no sign claim / no RH claim

---

## 0. Review result

The new implementation in

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
```

closes the intended P0/P1/P3/P4 surfaces.

Current classification:

```text
source-derived mirrored adjoint                         GREEN
source autocorrelation                                 GREEN
autocorrelation = aggregate normSq                     GREEN
autocorrelation integral = continuous Gram energy      GREEN
zero/vacuum section                                    GREEN
pointwise polarization                                 GREEN
finite t/u rectangle integrability                     OPEN
interval-integral order exchange                       OPEN
vertical source = normalized aggregate u-average       OPEN
whole scalar-excess quadraticization                   OPEN
prime-side sign                                        NOT CLAIMED
RH                                                     NOT CLAIMED
```

The current `PascalCenteredXiPrimeSideQuadraticizationLinearAggregateExchangeGap` is an appropriate audit marker. It records only the missing finite-rectangle certificate and does not assert impossibility.

---

## 1. P0/P1 review

The source autocorrelation is defined from the actual aggregate and the concrete mirrored finite source:

```text
AggregatedBoxFeature(W,X,u)
  * MirroredAggregatedBoxFeature(W,X,u).
```

The theorem

```lean
pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_eq_normSq
```

uses the already-proved mirrored-source conjugation identity, so the second factor retains source provenance.

The theorem

```lean
pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_integral_eq_gramEnergy
```

then identifies its normalized `u` integral with the existing continuous Gram energy.

This is a valid source-derived Hermitian product layer. It still does not identify the original linear vertical contour observable with this nonnegative energy.

---

## 2. P3/P4 review

The zero/vacuum section

```lean
mellinQuadraticBoxZeroSection
```

is correctly kept separate from the Gram diagonal. The exact identities

```text
mellinQuadraticBoxWeight = node * zeroSection
zeroSection = normalized exponential box average
```

make the one-variable RH weight a cross-pairing surface rather than pretending it is the Gram diagonal.

The pointwise polarization theorem is also exact:

$$
4F=|F+1|^2-|F-1|^2.
$$

Because the right-hand side is a difference of two nonnegative quantities, this theorem is an exact quadraticization identity but not a positivity theorem.

---

## 3. P2 is now a single finite-rectangle problem

The remaining linear-source bridge should target the exact identity

$$
V_{\varepsilon,X}(W)=((2\varepsilon)^{-1}:\mathbb C)\int_{-\varepsilon}^{\varepsilon}F_X(u)\,du.
$$

Here `V` is the existing genuine deoriented finite vertical source and `F_X` is `pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature`.

No limit, infinite series exchange, dominated-convergence theorem, or `T -> infinity` argument is required. The only nontrivial analytic step is exchanging two finite interval integrals.

Mathlib already provides the exact API:

```lean
MeasureTheory.intervalIntegral_intervalIntegral_swap
```

whose hypothesis is an `IntegrableOn` certificate for the uncurried two-variable integrand on the product of the two unordered interval sets.

Add the explicit import if it is not already available through the current import closure:

```lean
import Mathlib.MeasureTheory.Integral.Prod
```

Do not depend on a transitive import accidentally exposing the Fubini API.

---

## 4. P2-A — name the rectangle integrability certificate

Recommended theorem surface:

```lean
pascalCenteredXiPrimeSideQuadraticizationBoxFeature_integrableOn_rectangle
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    MeasureTheory.IntegrableOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
      volume
```

The exact pair order may be chosen to match the desired first iterated integral, but keep it fixed thereafter.

The certificate must be proved at finite `X`, finite `T`, and fixed positive `ε`.

---

## 5. Preferred integrability proof paths

### Route A — joint continuity on the compact rectangle

If the current Mathlib API makes the source amplitude regularity manageable, this is the cleanest route.

Prove continuity of

```text
(t,u) ↦ BoxFeature(W,X,t,u)
```

on the compact rectangle, then apply `ContinuousOn.integrableOn_compact` or `ContinuousOn.integrableOn_compact'`.

The prime finite PHZ and elementary correction should be straightforward. The archimedean factor is the only potentially expensive subgoal because it contains `logDeriv Gammaℝ`.

If this route is used, prove the archimedean regularity on the safe open half-plane `1 < re(s)` rather than globally. Mathlib's complex-analysis API states that a complex-differentiable function on an open set has differentiable derivative and is continuously differentiable there. This can be used after establishing differentiability and nonvanishing of `Gammaℝ` on the right half-plane.

Do not introduce a global continuity claim across Gamma poles merely to simplify the proof.

### Route B — finite-window domination from existing interval integrability

If Route A becomes disproportionately expensive, avoid proving global joint continuity.

For fixed `u`, the weight

```text
z ↦ z^2 * exp(u*z)
```

is entire. Reuse the existing finite right-edge integrability machinery for the finite PHZ plus correction source with this differentiable weight.

Then establish a uniform bound for `u ∈ [-ε,ε]`. On the right edge the real part of the centered node is constant, and both `u` and `t` range over compact intervals. Hence the exponential factor and polynomial node factor admit finite uniform bounds. Use these bounds to obtain product-set integrability.

This route is acceptable if it yields the exact `IntegrableOn` hypothesis required by `intervalIntegral_intervalIntegral_swap` without adding stronger analytic hypotheses.

Choose whichever route compiles more cleanly in the pinned Mathlib version. Do not keep both proof infrastructures unless both are independently useful.

---

## 6. P2-B — close the interval-integral swap

After P2-A is Green, prove a small dedicated theorem:

```lean
pascalCenteredXiPrimeSideQuadraticization_boxFeature_intervalIntegral_swap
```

with content equivalent to

```text
∫ t in -T..T, ∫ u in -ε..ε, BoxFeature t u
  =
∫ u in -ε..ε, ∫ t in -T..T, BoxFeature t u.
```

This theorem should be a thin wrapper around

```lean
MeasureTheory.intervalIntegral_intervalIntegral_swap
```

and the P2-A certificate.

Do not mix source reconstruction, normalization scalars, or polarization into this theorem.

---

## 7. P2-C — vertical source before the swap

Before using Fubini, expose the exact equality between the new quadraticization-layer vertical integral and the already-existing genuine vertical source.

Recommended intermediate definition or theorem:

```text
LinearVerticalSource(W,X,ε)
  := ∫ t in -T..T,
       pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand ε W X t
```

Then prove

```text
LinearVerticalSource(W,X,ε)
  = pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X.
```

The old whole-surface module already proves that the three deoriented component surfaces sum to `pascalCenteredXiMellinQuadraticComplexVerticalSurface`. Reuse that theorem rather than reconstructing the source orientation a second time.

The generic-weight adapter at `τ = 0` supplies the bridge between the new deoriented integrand and the old RH-weight integrand.

---

## 8. P2-D — assemble the exact linear aggregate identity

Use the existing pointwise theorem

```lean
pascalCenteredXiPrimeSideQuadraticization_boxFeature_integral_eq_weight_mul_amplitude
```

inside the `t` integral, move the constant `(2*ε)⁻¹` outside, apply P2-B, and fold the inner `t` integral into

```lean
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature.
```

Preferred final theorem surface:

```lean
pascalCenteredXiPrimeSideQuadraticizationComplexVerticalSurface_eq_normalized_aggregate_integral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u
```

Once this theorem is Green, the current `LinearAggregateExchangeGap` may be retired or replaced by a closeout marker.

---

## 9. What P2 would and would not prove

P2 Green would prove that the actual finite deoriented vertical explicit-formula source is exactly the normalized linear functional of the source-derived aggregate feature.

Combined with the already Green polarization theorem, this gives a legitimate quadratic difference representation for the vertical source.

It still would not prove positivity, because polarization produces a difference of two squared norms.

It also would not absorb the remaining terms of the whole scalar surface:

```text
top-horizontal contribution   still separate
radial comparison             still separate
whole scalar excess           still open
prime-side sign               still open
RH                            not claimed
```

Keep these firewalls unchanged.

---

## 10. Next checkpoint after P2

If P2 closes, the next audit should compare the two polarized energies rather than search for another adjoint.

Recommended sequence:

```text
P5  integrated polarization of actual vertical source
P6  identify the two shifted source energies
P7  search for a source-derived order between the shifted energies
P8  audit top-horizontal compatibility
P9  audit radial compatibility
P10 whole scalar-excess quadraticization or named obstruction
```

The key post-P2 question will be whether source structure orders the two polarized squared norms. Their individual nonnegativity alone is insufficient.
