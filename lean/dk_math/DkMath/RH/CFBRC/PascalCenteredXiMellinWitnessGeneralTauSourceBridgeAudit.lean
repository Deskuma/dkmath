/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import Mathlib.Tactic

/-!
# GWSS-003F: general-`τ` source-feature bridge audit

For nonzero `τ`, the canonical second-difference weight is the symmetric
exponential kernel multiplied by the Mellin box spectral weight.  This file
records the resulting logarithmic-box feature and transports it through the
finite right-edge and top-edge source amplitudes.

The statements are finite-window representation statements.  They retain the
finite arithmetic cutoff and do not assert positivity, a limit exchange, a
source-rank theorem, or RH.  In particular, the conditional rectangle bridge
below makes its Fubini hypothesis explicit rather than hiding an unavailable
integrability provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped BigOperators Interval Topology

/-! ## F1--F2: the nonzero-`τ` logarithmic-box feature -/

/-- The symmetric exponential kernel attached to a nonzero Mellin dilation. -/
noncomputable def pascalCenteredXiMellinGeneralTauBoxKernel
    (τ : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp ((τ : ℂ) * z) - 2 +
      Complex.exp (-(τ : ℂ) * z)) / (τ : ℂ) ^ 2

/-- The unnormalised logarithmic-box feature for the general-`τ` kernel. -/
noncomputable def pascalCenteredXiMellinGeneralTauBoxFeature
    (τ : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  pascalCenteredXiMellinGeneralTauBoxKernel τ z *
    Complex.exp ((u : ℂ) * z)

/-- The canonical weight is the normalised logarithmic-box average of the
general-`τ` feature, for `τ ≠ 0`. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_eq_normalized_generalTauBoxFeature_integral
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ z =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauBoxFeature τ z u) := by
  rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul hτ z,
    centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε z]
  unfold pascalCenteredXiMellinGeneralTauBoxFeature
    pascalCenteredXiMellinGeneralTauBoxKernel
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ## F3: finite right-edge source transport -/

/-- The general-`τ` box feature obtained by multiplying the right-edge source
amplitude by the corresponding logarithmic feature. -/
noncomputable def pascalCenteredXiMellinGeneralTauVerticalBoxFeature
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (t u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t *
  pascalCenteredXiMellinGeneralTauBoxFeature
      τ (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) u

/- The continuous kernel is named separately so that the finite source
amplitude can be combined with the existing product-rectangle certificate. -/
noncomputable def pascalCenteredXiMellinGeneralTauVerticalBoxKernel
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (t u : ℝ) : ℂ :=
  pascalCenteredXiMellinGeneralTauBoxFeature
    τ (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) u

theorem continuous_pascalCenteredXiMellinGeneralTauVerticalBoxKernel
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (Function.uncurry
      (pascalCenteredXiMellinGeneralTauVerticalBoxKernel τ W)) := by
  unfold pascalCenteredXiMellinGeneralTauVerticalBoxKernel
    pascalCenteredXiMellinGeneralTauBoxFeature
    pascalCenteredXiMellinGeneralTauBoxKernel
    pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
    pascalOrdinaryToCentered pascalSymmetricRectangleRightEdge
  fun_prop

/-- One nonzero-`τ` vertical source fibre averages to the specialized weight
times the finite source amplitude. -/
theorem pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integral_eq_weight_mul_amplitude
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X t u) =
      pascalCenteredXiMellinSecondDifferenceWeight ε τ
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  unfold pascalCenteredXiMellinGeneralTauVerticalBoxFeature
  rw [intervalIntegral.integral_const_mul,
    pascalCenteredXiMellinSecondDifferenceWeight_eq_normalized_generalTauBoxFeature_integral
      hε hτ]
  ring

/-- The finite right-edge source feature aggregated over the contour height. -/
noncomputable def pascalCenteredXiMellinGeneralTauVerticalAggregatedBoxFeature
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (u : ℝ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X t u

/-- The vertical source bridge is exact once the displayed finite rectangle
feature is known to be integrable.  This is the precise remaining analytic
interface for a fully unconditional general-`τ` source theorem. -/
theorem pascalCenteredXiMellinGeneralTau_weighted_vertical_source_eq_normalized_aggregate_of_rectangle_integrable
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X))
        (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
        volume) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiMellinSecondDifferenceWeight ε τ
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauVerticalAggregatedBoxFeature τ W X u := by
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinSecondDifferenceWeight ε τ
            (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X t u := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact
            (pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integral_eq_weight_mul_amplitude
              hε hτ W X t).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X t u := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ∫ t in (-W.rectangle.T)..W.rectangle.T,
            pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X t u := by
          rw [intervalIntegral_intervalIntegral_swap hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauVerticalAggregatedBoxFeature τ W X u := by
          simp only [pascalCenteredXiMellinGeneralTauVerticalAggregatedBoxFeature]

/-- The general-`τ` vertical rectangle feature is integrable at every finite
cutoff.  The proof uses continuity of the new kernel and the existing finite
source-amplitude product certificate. -/
theorem pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integrableOn_rectangle
    (ε τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
      volume := by
  let A : Set ℝ := Set.uIoc (-W.rectangle.T) W.rectangle.T
  let B : Set ℝ := Set.uIoc (-ε) ε
  let K : Set (ℝ × ℝ) :=
    Set.uIcc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIcc (-ε) ε
  have hamp : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
          (1 : ℂ)) (A ×ˢ B) volume := by
    simpa only [A, B] using
      pascalCenteredXiPrimeSideQuadraticization_verticalAmplitude_product_integrable
        ε W X
  have hK : IsCompact K := by
    exact isCompact_uIcc.prod isCompact_uIcc
  have hABK : A ×ˢ B ⊆ K := by
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have hmul : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiMellinGeneralTauVerticalBoxKernel τ W p.1 p.2 *
          (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
            (1 : ℂ))) (A ×ˢ B) volume :=
    IntegrableOn.continuousOn_mul_of_subset
      (continuous_pascalCenteredXiMellinGeneralTauVerticalBoxKernel τ W).continuousOn
      hamp hK (measurableSet_uIoc.prod measurableSet_uIoc) hABK
  have heq :
      Function.uncurry
          (pascalCenteredXiMellinGeneralTauVerticalBoxFeature τ W X) =
        (fun p : ℝ × ℝ =>
          pascalCenteredXiMellinGeneralTauVerticalBoxKernel τ W p.1 p.2 *
            (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
              (1 : ℂ))) := by
    funext p
    change
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
          pascalCenteredXiMellinGeneralTauBoxFeature
            τ (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1) p.2 =
        pascalCenteredXiMellinGeneralTauBoxFeature
            τ (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1) p.2 *
          (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
            (1 : ℂ))
    simp only [mul_one]
    ring
  rw [heq]
  simpa only [A, B, mul_one] using hmul

/- The finite right-edge bridge with its integrability provider discharged. -/
theorem pascalCenteredXiMellinGeneralTau_weighted_vertical_source_eq_normalized_aggregate
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiMellinSecondDifferenceWeight ε τ
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauVerticalAggregatedBoxFeature τ W X u := by
  exact
    pascalCenteredXiMellinGeneralTau_weighted_vertical_source_eq_normalized_aggregate_of_rectangle_integrable
      hε hτ W X
      (pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integrableOn_rectangle
        ε τ W X)

/-! ## F4: top-horizontal source fibre -/

/-- The general-`τ` box feature carried by the finite top-horizontal source. -/
noncomputable def pascalCenteredXiMellinGeneralTauTopBoxFeature
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x *
    pascalCenteredXiMellinGeneralTauBoxFeature
      τ (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) v

noncomputable def pascalCenteredXiMellinGeneralTauTopBoxKernel
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x v : ℝ) : ℂ :=
  pascalCenteredXiMellinGeneralTauBoxFeature
    τ (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) v

theorem continuous_pascalCenteredXiMellinGeneralTauTopBoxKernel
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (Function.uncurry
      (pascalCenteredXiMellinGeneralTauTopBoxKernel τ W)) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationTopNode W) :=
    continuous_pascalCenteredXiPrimeSideQuadraticizationTopNode W
  have hnode' : Continuous (fun p : ℝ × ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) :=
    hnode.comp continuous_fst
  unfold pascalCenteredXiMellinGeneralTauTopBoxKernel
    pascalCenteredXiMellinGeneralTauBoxFeature
    pascalCenteredXiMellinGeneralTauBoxKernel
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ((Complex.exp ((τ : ℂ) *
          pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) - 2 +
        Complex.exp (-(τ : ℂ) *
          pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1)) /
        (τ : ℂ) ^ 2) *
        Complex.exp ((p.2 : ℂ) *
          pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1)) := by
    fun_prop
  convert hcont using 1
  rfl

/-- A top-horizontal source fibre has the same exact averaging identity as a
right-edge fibre. -/
theorem pascalCenteredXiMellinGeneralTauTopBoxFeature_integral_eq_weight_mul_amplitude
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauTopBoxFeature τ W x v) =
      pascalCenteredXiMellinSecondDifferenceWeight ε τ
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
  unfold pascalCenteredXiMellinGeneralTauTopBoxFeature
  rw [intervalIntegral.integral_const_mul,
    pascalCenteredXiMellinSecondDifferenceWeight_eq_normalized_generalTauBoxFeature_integral
      hε hτ]
  ring

/-! ## F4: top-horizontal source aggregation -/

/-- The general-`τ` top-horizontal feature aggregated over the finite edge. -/
noncomputable def pascalCenteredXiMellinGeneralTauTopAggregatedBoxFeature
    (τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiMellinGeneralTauTopBoxFeature τ W x v

/-- The top-horizontal source is transported into the general-`τ` feature
under the explicit finite-rectangle Fubini hypothesis.  The factor `I` is
not inserted here: this theorem identifies the horizontal source term itself,
before the contour orientation factor used by the surrounding explicit
formula. -/
theorem pascalCenteredXiMellinGeneralTau_top_horizontal_source_eq_normalized_aggregate_of_rectangle_integrable
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiMellinGeneralTauTopBoxFeature τ W))
        (Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ
          Set.uIoc (-ε) ε)
        volume) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.toContourTransportWindow =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauTopAggregatedBoxFeature τ W v := by
  unfold pascalCenteredXiTopHorizontalContribution
  calc
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiWeightedNegLogDeriv
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge x W.rectangle.T))) =
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε τ
            (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with x hx
          rfl
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauTopBoxFeature τ W x v := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with x hx
          exact
            (pascalCenteredXiMellinGeneralTauTopBoxFeature_integral_eq_weight_mul_amplitude
              hε hτ W x).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          ∫ v in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauTopBoxFeature τ W x v := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiMellinGeneralTauTopBoxFeature τ W x v := by
          rw [intervalIntegral_intervalIntegral_swap hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauTopAggregatedBoxFeature τ W v := by
          simp only [pascalCenteredXiMellinGeneralTauTopAggregatedBoxFeature]

/-- Integrability of the general-`τ` top feature follows from the existing
finite top-amplitude interval certificate and compact continuity of the new
kernel. -/
theorem pascalCenteredXiMellinGeneralTauTopBoxFeature_integrableOn_rectangle
    (ε τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauTopBoxFeature τ W))
      (Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ
        Set.uIoc (-ε) ε)
      volume := by
  let A : Set ℝ := Set.uIoc W.rectangle.σ (1 - W.rectangle.σ)
  let B : Set ℝ := Set.uIoc (-ε) ε
  let K : Set (ℝ × ℝ) :=
    Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ Set.uIcc (-ε) ε
  have hamp : IntegrableOn
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W) A volume := by
    exact intervalIntegrable_iff.mp
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_intervalIntegrable W)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℂ)) B volume := by
    exact intervalIntegrable_iff.mp
      (intervalIntegrable_const (μ := volume) (a := -ε) (b := ε))
  have hampProd : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1 *
          (1 : ℂ)) (A ×ˢ B) volume := by
    change Integrable
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1 *
          (1 : ℂ)) (volume.restrict (A ×ˢ B))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hamp.mul_prod hone
  have hampLift : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1)
      (A ×ˢ B) volume := by
    simpa using hampProd
  have hK : IsCompact K := by
    exact isCompact_uIcc.prod isCompact_uIcc
  have hAK : A ×ˢ B ⊆ K := by
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have hmul : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiMellinGeneralTauTopBoxKernel τ W p.1 p.2 *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1)
      (A ×ˢ B) volume :=
    IntegrableOn.continuousOn_mul_of_subset
      (continuous_pascalCenteredXiMellinGeneralTauTopBoxKernel τ W).continuousOn
      hampLift hK (measurableSet_uIoc.prod measurableSet_uIoc) hAK
  have heq :
      Function.uncurry
          (pascalCenteredXiMellinGeneralTauTopBoxFeature τ W) =
        (fun p : ℝ × ℝ =>
          pascalCenteredXiMellinGeneralTauTopBoxKernel τ W p.1 p.2 *
            pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1) := by
    funext p
    change
      pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1 *
          pascalCenteredXiMellinGeneralTauBoxFeature
            τ (pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) p.2 =
        pascalCenteredXiMellinGeneralTauBoxFeature
            τ (pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) p.2 *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1
    ring
  rw [heq]
  simpa only [A, B] using hmul

/-- The finite top-horizontal bridge with its integrability provider
discharged. -/
theorem pascalCenteredXiMellinGeneralTau_top_horizontal_source_eq_normalized_aggregate
    {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.toContourTransportWindow =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauTopAggregatedBoxFeature τ W v := by
  exact
    pascalCenteredXiMellinGeneralTau_top_horizontal_source_eq_normalized_aggregate_of_rectangle_integrable
      hε hτ W
      (pascalCenteredXiMellinGeneralTauTopBoxFeature_integrableOn_rectangle ε τ W)

/-! ## F5: finite synthesized target witness -/

/-- The logarithmic-box feature synthesized with the same finite coefficients
as the GWSS-002 target witness. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ) (u : ℝ) : ℂ :=
  ∑ i, c i * pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u

/-- Every finite synthesized witness with nonzero selected dilations has the
same exact normalized logarithmic-box representation.  This is a finite sum
identity; it does not turn the source feature into a Gram positivity theorem.
-/
theorem pascalCenteredXiMellinWitnessWeight_eq_normalized_generalTauWitnessBoxFeature_integral
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (z : ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ c z =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessBoxFeature τ c z u := by
  classical
  have hInt : ∀ i : Fin n,
      IntervalIntegrable
        (fun u : ℝ => c i *
          pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u)
        volume (-ε) ε := by
    intro i
    apply Continuous.intervalIntegrable
    unfold pascalCenteredXiMellinGeneralTauBoxFeature
      pascalCenteredXiMellinGeneralTauBoxKernel
    fun_prop
  have hsum := intervalIntegral_sum_univ_eq_sum_intervalIntegral hInt
  unfold pascalCenteredXiMellinWitnessWeight
    pascalCenteredXiMellinGeneralTauWitnessBoxFeature
  calc
    (∑ i, c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) z) =
        ∑ i, c i *
          (((2 * ε : ℝ)⁻¹ : ℂ) *
            ∫ u in (-ε)..ε,
              pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_normalized_generalTauBoxFeature_integral
            hε (hτ i) z]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∑ i, ∫ u in (-ε)..ε,
          c i * pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u := by
          simp_rw [intervalIntegral.integral_const_mul]
          calc
            (∑ i, c i * (((2 * ε : ℝ)⁻¹ : ℂ) *
                ∫ u in (-ε)..ε,
                  pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u)) =
                ∑ i, ((2 * ε : ℝ)⁻¹ : ℂ) *
                  (c i * ∫ u in (-ε)..ε,
                    pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
                ∑ i, c i * ∫ u in (-ε)..ε,
                  pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u := by
                    rw [Finset.mul_sum]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ∑ i, c i * pascalCenteredXiMellinGeneralTauBoxFeature (τ i) z u := by
          rw [hsum]

/-- The finite synthesized witness feature carried by the right-edge source
amplitude. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (t u : ℝ) : ℂ :=
  ∑ i, c i * pascalCenteredXiMellinGeneralTauVerticalBoxFeature
    (τ i) W X t u

/-- The general-`τ` logarithmic feature also transports a finite synthesized
GWSS-002 witness through each right-edge source fibre. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integral_eq_witnessWeight_mul_amplitude
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u) =
      pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  classical
  have hInt : ∀ i : Fin n,
      IntervalIntegrable
        (fun u : ℝ => c i *
          pascalCenteredXiMellinGeneralTauVerticalBoxFeature
            (τ i) W X t u) volume (-ε) ε := by
    intro i
    apply Continuous.intervalIntegrable
    unfold pascalCenteredXiMellinGeneralTauVerticalBoxFeature
      pascalCenteredXiMellinGeneralTauBoxFeature
      pascalCenteredXiMellinGeneralTauBoxKernel
    fun_prop
  have hsum := intervalIntegral_sum_univ_eq_sum_intervalIntegral hInt
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ∑ i, c i * pascalCenteredXiMellinGeneralTauVerticalBoxFeature
            (τ i) W X t u =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∑ i, ∫ u in (-ε)..ε,
          c i * pascalCenteredXiMellinGeneralTauVerticalBoxFeature
            (τ i) W X t u := by
          rw [hsum]
    _ = ∑ i, c i *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauVerticalBoxFeature
              (τ i) W X t u) := by
          simp_rw [intervalIntegral.integral_const_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i, c i *
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
            (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integral_eq_weight_mul_amplitude
            hε (hτ i) W X t]
    _ = pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
          unfold pascalCenteredXiMellinWitnessWeight
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- The synthesized finite right-edge source feature aggregated over height. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u

/-- The general-`τ` source bridge lifts through a finite synthesized witness
on the right edge, including the finite rectangle Fubini step. -/
theorem pascalCenteredXiMellinGeneralTauWitness_weighted_vertical_source_eq_normalized_aggregate
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X))
        (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
        volume) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
            τ c W X u := by
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinWitnessWeight ε τ c
            (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact
            (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integral_eq_witnessWeight_mul_amplitude
              hε τ c hτ W X t).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ∫ t in (-W.rectangle.T)..W.rectangle.T,
            pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u := by
          rw [intervalIntegral_intervalIntegral_swap hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
            τ c W X u := by
          simp only [pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature]

/-! ## F7: fixed complex references -/

/-- Polarization against the real reference `1` extracts the real component
of an arbitrary complex feature. -/
theorem normSq_shifted_difference_one_eq_four_mul_re (F : ℂ) :
    (Complex.normSq (F + 1) : ℂ) - Complex.normSq (F - 1) =
      (4 : ℂ) * F.re := by
  apply Complex.ext <;> simp [Complex.normSq]
  all_goals ring

/-- Polarization against the imaginary reference `I` extracts the imaginary
component of an arbitrary complex feature. -/
theorem normSq_shifted_difference_I_eq_four_mul_im (F : ℂ) :
    (Complex.normSq (F + Complex.I) : ℂ) - Complex.normSq (F - Complex.I) =
      (4 : ℂ) * F.im := by
  apply Complex.ext <;> simp [Complex.normSq]
  all_goals ring

end DkMath.RH.CFBRCProjection
