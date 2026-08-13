# IPSM-020 — P2-A finite-rectangle integrability certificate roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Target module:

`lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean`

Status:

- P0 source-derived adjoint: Green
- P1 source autocorrelation / Gram energy: Green
- P2-A rectangle `IntegrableOn` certificate: Open
- P2-B interval-integral swap wrapper: Green
- P2-D normalized aggregate bridge under `hbox`: Green
- P3 zero/vacuum section: Green
- P4 pointwise polarization: Green
- prime-side sign: not claimed
- whole scalar-excess PSD identity: not claimed
- RH: not claimed

---

## 0. Purpose

Close the only remaining analytic certificate required by the current P2 bridge:

```lean
IntegrableOn
  (Function.uncurry
    (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
  (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
  volume
```

Do not prove this by forcing joint continuity of the whole `BoxFeature`.

Preferred route:

```text
BoxFeature(t,u)
  = continuous bounded kernel factor G(t,u)
    * t-only vertical amplitude A_X(t)
```

Then lift one-variable integrability of `A_X(t)` to the finite rectangle and multiply by the continuous factor on a compact superset.

This keeps the Gamma/logDeriv part out of the joint-continuity obligation.

---

## 1. Existing P2-B / P2-D surfaces

The current wrapper

```lean
pascalCenteredXiPrimeSideQuadraticization_boxFeature_intervalIntegral_swap
```

correctly delegates the finite rectangle exchange to

```lean
intervalIntegral_intervalIntegral_swap hbox
```

and

```lean
pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate_of_rectangle_integrable
```

correctly requires `hbox` explicitly.

Do not weaken these theorems. The task is to construct the concrete `hbox`.

---

## 2. P2-A1 — vertical amplitude interval integrability

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
      volume (-W.rectangle.T) W.rectangle.T := by
  ...
```

The amplitude is the finite PHZ term plus archimedean and elementary corrections.

For the finite PHZ term, reuse the finite Dirichlet-polynomial continuity proof pattern already present in `PascalCenteredXiPrimeRightEdgeTransport.lean`, based on the finite L-series partial sum and `continuous_const_cpow`.

Do not replace the finite PHZ by its `X → ∞` limit.

For the non-prime component, avoid reproving Gamma derivative continuity if possible. Reuse:

```lean
intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
```

with constant centered weight `fun _ => 1`.

Transport away the trailing `Complex.I` algebraically to recover interval integrability of the archimedean + elementary amplitude.

Finally combine the prime and non-prime pieces with `.add`.

---

## 3. P2-A2 — separate the bounded continuous kernel

Introduce a helper kernel if useful:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) (t u : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) ^ 2 *
    Complex.exp
      ((u : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)
```

Then expose:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationBoxFeature_eq_kernel_mul_amplitude
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u =
      pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  rfl
```

or the equivalent theorem matching the actual definition.

Prove joint continuity only for this kernel:

```lean
theorem continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) :
    Continuous
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxKernel W)) := by
  ...
```

`fun_prop` may work here because Gamma/logDeriv has been removed.

---

## 4. P2-A3 — lift the amplitude to the product rectangle

Let the finite rectangle be

```text
Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε.
```

Convert the `IntervalIntegrable` amplitude to `IntegrableOn` on the `t` interval.

Then lift the `t`-only function to the product rectangle.

Two acceptable approaches:

```text
Route A: Integrable.comp_fst
Route B: Integrable.mul_prod with the u-side constant 1
```

Keep everything on finite restricted measures.

No infinite-rectangle result is required.

---

## 5. P2-A4 — multiply by the continuous kernel

Use the compact superset

```text
Set.uIcc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIcc (-ε) ε
```

and the standard inclusion from `uIoc` into `uIcc`.

Combine:

- the product-lifted amplitude `IntegrableOn`,
- joint continuity of the kernel,
- compactness/boundedness on the superset,

using the available `IntegrableOn.continuousOn_mul_of_subset` family or an equivalent Mathlib theorem.

Target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_boxFeature_integrableOn_rectangle
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ
        Set.uIoc (-ε) ε)
      volume := by
  ...
```

A positivity assumption on `ε` should not be added unless an existing helper API requires it.

---

## 6. P2-A5 — unconditional normalized aggregate bridge

Once the concrete rectangle certificate is Green, close:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
  exact
    pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate_of_rectangle_integrable
      hε W X
      (pascalCenteredXiPrimeSideQuadraticization_boxFeature_integrableOn_rectangle
        (ε := ε) W X)
```

Adjust argument order to the actual signatures.

---

## 7. P2-C/D — connect to the genuine vertical source

Reuse existing whole-surface theorems:

```lean
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_weight_mul_decomposed
```

and

```lean
pascalCenteredXiMellinQuadraticDeorientedSurfaces_eq_complexVerticalSurface
```

to reach the existing genuine complex vertical source.

Final target:

```lean
theorem pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
  ...
```

Do not manufacture a new orientation convention.

---

## 8. Acceptance criteria

P2-A is Green only when:

```text
[ ] finite PHZ t-integrability is proved at fixed finite X
[ ] non-prime t-integrability reuses the existing safe right-edge theorem
[ ] no X → ∞ argument is used
[ ] no ε → 0 argument is used
[ ] no T → ∞ argument is used
[ ] no joint-continuity assumption is made for Gamma/logDeriv
[ ] BoxFeature rectangle IntegrableOn is proved concretely
[ ] intervalIntegral_intervalIntegral_swap receives that certificate
[ ] actual complex vertical source equals normalized u-average of the aggregate
[ ] top-horizontal term remains separate
[ ] radial comparison remains separate
[ ] no sign theorem is claimed
[ ] no RH consequence is claimed
```

---

## 9. What P2 completion establishes

If P2 closes, the exact finite source identity is:

$$
V_{\varepsilon,X}(W)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}F_X(u)\,du.
$$

Together with aggregate reality:

$$
F_X(u)=\overline{F_X(u)}.
$$

and pointwise polarization:

$$
4F_X(u)=|F_X(u)+1|^2-|F_X(u)-1|^2.
$$

this gives a source-derived quadraticization of the vertical linear observable as a difference of two nonnegative square energies.

It still does not give a sign because no order between the two square energies has been established.

Post-P2 questions remain:

```text
Q1  Can the source structure order the +1 and -1 shifted energies?
Q2  Can the top-horizontal contribution enter the same quadratic structure?
Q3  Can the radial subtraction be represented or bounded compatibly?
Q4  Can the whole scalar excess be identified with or bounded by a PSD quantity?
```

---

## 10. Firewall

Keep explicit:

```text
vertical source quadraticization
  != vertical source nonnegativity

vertical source nonnegativity
  != whole finite scalar-excess sign

whole finite scalar-excess sign
  != RH
```

Do not use zero-side anti-mirror energy to prove the prime-side sign.

Do not absorb the top-horizontal contribution into vertical energy by definition.

Do not absorb radial comparison into a PSD term without an exact theorem.

Do not exchange the established limit order.

P2 itself remains entirely finite in `X`, `T`, and `ε`.
