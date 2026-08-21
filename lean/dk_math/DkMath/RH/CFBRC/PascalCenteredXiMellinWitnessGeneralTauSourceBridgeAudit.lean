/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit
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

/-! ## F4.2: synthesized top-horizontal source -/

/-- The finite synthesized top-horizontal feature, with the GWSS-002
coefficients retained term by term. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) : ℂ :=
  ∑ i, c i * pascalCenteredXiMellinGeneralTauTopBoxFeature (τ i) W x v

/-- The normalized top-horizontal source feature of a synthesized witness. -/
theorem pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integral_eq_witnessWeight_mul_amplitude
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v) =
      pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
  classical
  have hInt : ∀ i : Fin n,
      IntervalIntegrable
        (fun v : ℝ => c i *
          pascalCenteredXiMellinGeneralTauTopBoxFeature (τ i) W x v)
        volume (-ε) ε := by
    intro i
    apply Continuous.intervalIntegrable
    unfold pascalCenteredXiMellinGeneralTauTopBoxFeature
      pascalCenteredXiMellinGeneralTauBoxFeature
      pascalCenteredXiMellinGeneralTauBoxKernel
    fun_prop
  have hsum := intervalIntegral_sum_univ_eq_sum_intervalIntegral hInt
  unfold pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          ∑ i, c i * pascalCenteredXiMellinGeneralTauTopBoxFeature (τ i) W x v =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∑ i, ∫ v in (-ε)..ε,
          c i * pascalCenteredXiMellinGeneralTauTopBoxFeature (τ i) W x v := by
          rw [hsum]
    _ = ∑ i, c i *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauTopBoxFeature (τ i) W x v) := by
          simp_rw [intervalIntegral.integral_const_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i, c i *
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
            (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pascalCenteredXiMellinGeneralTauTopBoxFeature_integral_eq_weight_mul_amplitude
            hε (hτ i) W x]
    _ = pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
          unfold pascalCenteredXiMellinWitnessWeight
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- The synthesized top feature is integrable on each finite source
rectangle by finite-sum closure of the single-basis top certificate. -/
theorem pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integrableOn_rectangle
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W))
      (Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ Set.uIoc (-ε) ε)
      volume := by
  classical
  let S : Set (ℝ × ℝ) :=
    Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ Set.uIoc (-ε) ε
  change Integrable
    (fun p : ℝ × ℝ =>
      ∑ i, c i * pascalCenteredXiMellinGeneralTauTopBoxFeature
        (τ i) W p.1 p.2)
    (volume.restrict S)
  apply integrable_finsetSum (μ := volume.restrict S) (Finset.univ : Finset (Fin n))
  intro i hi
  exact
    (pascalCenteredXiMellinGeneralTauTopBoxFeature_integrableOn_rectangle
      ε (τ i) W).integrable.const_mul (c i)

/-- The synthesized top feature aggregated over the finite edge. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v

/-- The actual synthesized witness top-horizontal contribution is the
normalized integral of the synthesized top feature. -/
theorem pascalCenteredXiMellinGeneralTauWitness_top_horizontal_source_eq_normalized_aggregate
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.toContourTransportWindow =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
            τ c W v := by
  have hbox :=
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integrableOn_rectangle
      ε τ c W
  unfold pascalCenteredXiTopHorizontalContribution
  calc
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiWeightedNegLogDeriv
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge x W.rectangle.T))) =
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinWitnessWeight ε τ c
            (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with x hx
          rfl
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with x hx
          exact
            (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integral_eq_witnessWeight_mul_amplitude
              hε τ c hτ W x).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          ∫ v in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v := by
          rw [intervalIntegral_intervalIntegral_swap hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ c W v := by
          simp only [pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature]

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

/-- Finite coefficient sums preserve the already-proved single-basis
rectangle integrability of the right-edge source feature. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integrableOn_rectangle
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
      volume := by
  classical
  let S : Set (ℝ × ℝ) :=
    Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε
  change Integrable
    (fun p : ℝ × ℝ =>
      ∑ i, c i * pascalCenteredXiMellinGeneralTauVerticalBoxFeature
        (τ i) W X p.1 p.2)
    (volume.restrict S)
  apply integrable_finsetSum (μ := volume.restrict S) (Finset.univ : Finset (Fin n))
  intro i hi
  exact
    (pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integrableOn_rectangle
      ε (τ i) W X).integrable.const_mul (c i)

/-- The general-`τ` source bridge lifts through a finite synthesized witness
on the right edge, including the finite rectangle Fubini step. -/
theorem pascalCenteredXiMellinGeneralTauWitness_weighted_vertical_source_eq_normalized_aggregate
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
            τ c W X u := by
  have hbox :=
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integrableOn_rectangle
      ε τ c W X
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

/-! ## F6: synthesized whole-source assembly -/

/-! ## F5.5: outer-variable integrability adapters -/

/-- Fubini converts the synthesized vertical rectangle certificate into
interval-integrability of the outer logarithmic feature variable.  The
restricted product measure is made explicit so that this theorem does not
use totalized interval integrals as an integrability assumption. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_intervalIntegrable
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ c W X) volume (-ε) ε := by
  let A : Set ℝ := Set.uIoc (-W.rectangle.T) W.rectangle.T
  let B : Set ℝ := Set.uIoc (-ε) ε
  have hbox :=
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integrableOn_rectangle
      ε τ c W X
  have hbox' : Integrable
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X))
      (volume.restrict (A ×ˢ B)) := hbox
  have hprod : Integrable
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X))
      ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict A B] at hbox'
    exact hbox'
  have hfib := hprod.swap.integral_prod_left
  rw [intervalIntegrable_iff]
  change Integrable
    (fun u : ℝ =>
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X t u)
    (volume.restrict B)
  have hT : -W.rectangle.T ≤ W.rectangle.T := by
    linarith [W.rectangle.hT]
  have heq :
      (fun u : ℝ =>
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
            τ c W X t u) =
      (fun u : ℝ =>
        ∫ t in A, (Function.uncurry
          (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ c W X)
            (t, u))) := by
    funext u
    rw [intervalIntegral.integral_of_le hT]
    simp only [A, Set.uIoc_of_le hT, Function.uncurry_apply_pair]
  rw [heq]
  simpa only [A, B, Function.comp_def, Prod.swap, Function.uncurry_apply_pair] using hfib

/-- Fubini likewise converts the synthesized top rectangle certificate into
interval-integrability on its (possibly oppositely oriented) horizontal
edge. -/
theorem pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_intervalIntegrable
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
        τ c W) volume (-ε) ε := by
  let A : Set ℝ := Set.uIoc W.rectangle.σ (1 - W.rectangle.σ)
  let B : Set ℝ := Set.uIoc (-ε) ε
  have hbox :=
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integrableOn_rectangle
      ε τ c W
  have hbox' : Integrable
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W))
      (volume.restrict (A ×ˢ B)) := hbox
  have hprod : Integrable
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W))
      ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict A B] at hbox'
    exact hbox'
  have hfib := hprod.swap.integral_prod_left
  rw [intervalIntegrable_iff]
  change Integrable
    (fun v : ℝ =>
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W x v)
    (volume.restrict B)
  by_cases hσ : W.rectangle.σ ≤ 1 - W.rectangle.σ
  · have heq :
        (fun v : ℝ =>
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
              τ c W x v) =
          (fun v : ℝ =>
          ∫ x in A, (Function.uncurry
            (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W)
              (x, v))) := by
      funext v
      rw [intervalIntegral.integral_of_le hσ]
      simp only [A, Set.uIoc_of_le hσ, Function.uncurry_apply_pair]
    rw [heq]
    simpa only [A, B, Function.comp_def, Prod.swap, Function.uncurry_apply_pair] using hfib
  · have hσ' : 1 - W.rectangle.σ ≤ W.rectangle.σ := le_of_not_ge hσ
    have heq :
        (fun v : ℝ =>
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
              τ c W x v) =
        (fun v : ℝ => -∫ x in A, (Function.uncurry
            (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ c W)
              (x, v))) := by
      funext v
      rw [intervalIntegral.integral_of_ge hσ']
      simp only [A, Set.uIoc_of_ge hσ', Function.uncurry_apply_pair]
    rw [heq]
    simpa only [neg_one_mul, Function.comp_def, Prod.swap,
      Function.uncurry_apply_pair] using (hfib.const_mul (-1))

/-- The deoriented vertical source attached to a synthesized witness.

The three finite right-edge arithmetic terms are represented by the source
amplitude.  The contour factor `Complex.I` is intentionally absent here; it
is restored in the finite arithmetic assembly below. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessVerticalSource
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinWitnessWeight ε τ c
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t

/-- The whole finite source, with the orientation convention
`2 * I * (vertical - I * top)` used by the finite ledger. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessWholeSource
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ c W X -
    Complex.I * pascalCenteredXiTopHorizontalContribution
      (pascalCenteredXiMellinWitnessWeight ε τ c)
      W.toContourTransportWindow

/-- The synthesized whole source feature.  It retains both the vertical and
top-horizontal aggregates and therefore does not silently discard the finite
top term. -/
noncomputable def pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
    {n : ℕ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
      τ c W X u -
    Complex.I * pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
      τ c W u

/-- The normalized whole-source bridge, conditional only on the two scalar
interval-integrability facts needed to integrate the displayed difference.
The vertical and top source representations themselves are unconditional
finite-rectangle statements proved above. -/
theorem pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate_of_integrable
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hV : IntervalIntegrable
      (pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ c W X) volume (-ε) ε)
    (hT : IntervalIntegrable
      (pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
        τ c W) volume (-ε) ε) :
    pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u := by
  rw [pascalCenteredXiMellinGeneralTauWitnessWholeSource,
    pascalCenteredXiMellinGeneralTauWitnessVerticalSource]
  rw [pascalCenteredXiMellinGeneralTauWitness_weighted_vertical_source_eq_normalized_aggregate
    hε τ c hτ W X]
  rw [pascalCenteredXiMellinGeneralTauWitness_top_horizontal_source_eq_normalized_aggregate
    hε τ c hτ W]
  simp only [pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature]
  have hIT := hT.const_mul Complex.I
  have hsub := intervalIntegral.integral_sub hV hIT
  rw [hsub, intervalIntegral.integral_const_mul]
  ring

/-- Unconditional whole-source normalization for a finite synthesized
nonzero-`τ` witness.  The two outer interval-integrability facts are supplied
by the restricted-product Fubini adapters above. -/
theorem pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u := by
  exact pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate_of_integrable
    hε τ c hτ W X
    (pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_intervalIntegrable
      ε τ c W X)
    (pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_intervalIntegrable
      ε τ c W)

/-! ## F6.1: arbitrary-weight vertical ledger -/

/-- The arbitrary differentiable weight has an interval-integrable finite
prime cutoff source.  The finite cutoff is handled locally by continuity of
the finite von-Mangoldt sum; no cutoff limit is used. -/
theorem pascalCenteredXiMellinGeneralTau_vertical_prime_integrable
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalPrimePowerRightEdgeCutoffIntegrand h W.rectangle.σ X)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ => (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hweight : Continuous (fun t : ℝ =>
      h (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) := by
    apply hh.continuous.comp
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t - criticalLineCenter)
    convert hpath.sub continuous_const using 1
    all_goals ext t; rfl
  have hterm : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) 0) =
        (fun _ : ℝ => 0) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
        simp
      rw [hz]
      exact continuous_const
    · letI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
      have hnterm : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) =
        (fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      convert continuous_const.mul
          ((continuous_const_cpow (n : ℂ)).comp
            (continuous_neg.comp hpath)) using 1
      all_goals ext t; rfl
  have hsum : Continuous (fun t : ℝ =>
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  have hphz : Continuous (fun t : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
    have heq : (fun t : ℝ =>
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) =
      (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) := by
      funext t
      exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _
    rw [heq]
    exact hsum
  have hcont := ((hweight.mul hphz).mul
      (continuous_const : Continuous (fun _ : ℝ => Complex.I))).intervalIntegrable
      (μ := volume) (-W.rectangle.T) W.rectangle.T
  apply hcont.congr
  intro t ht
  rfl

/-- The finite right-edge ledger is an exact oriented identity for every
differentiable complex weight.  Each of the prime, archimedean, and
elementary terms retains its `Complex.I` factor before the pointwise sum is
identified with the deoriented vertical amplitude. -/
theorem pascalCenteredXiMellinGeneralTau_vertical_source_ledger
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    2 * pascalPrimePowerRightEdgeCutoffIntegral h
        W.rectangle.σ W.rectangle.T X +
      2 * pascalXiArchimedeanRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T =
    2 * Complex.I *
      (∫ t in (-W.rectangle.T)..W.rectangle.T,
        h (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
  have hprime := pascalCenteredXiMellinGeneralTau_vertical_prime_integrable hh W X
  have harch := intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand hh W
  have helem := intervalIntegrable_pascalXiElementaryRightEdgeIntegrand hh W
  have hpoint : ∀ t : ℝ,
      pascalPrimePowerRightEdgeCutoffIntegrand h W.rectangle.σ X t +
          pascalXiArchimedeanRightEdgeIntegrand h W.rectangle.σ t +
        pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ t =
      Complex.I *
        (h (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
    intro t
    simp only [pascalPrimePowerRightEdgeCutoffIntegrand,
      pascalXiArchimedeanRightEdgeIntegrand,
      pascalXiElementaryRightEdgeIntegrand,
      pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode,
      pascalOrdinaryToCentered,
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude]
    ring
  calc
    2 * pascalPrimePowerRightEdgeCutoffIntegral h
          W.rectangle.σ W.rectangle.T X +
        2 * pascalXiArchimedeanRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T =
        2 * (pascalPrimePowerRightEdgeCutoffIntegral h
          W.rectangle.σ W.rectangle.T X +
          pascalXiArchimedeanRightEdgeIntegral h
            W.rectangle.σ W.rectangle.T +
          pascalXiElementaryRightEdgeIntegral h
            W.rectangle.σ W.rectangle.T) := by ring
    _ = 2 * ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (pascalPrimePowerRightEdgeCutoffIntegrand h W.rectangle.σ X t +
            pascalXiArchimedeanRightEdgeIntegrand h W.rectangle.σ t) +
            pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ t := by
          simp only [pascalPrimePowerRightEdgeCutoffIntegral,
            pascalXiArchimedeanRightEdgeIntegral,
            pascalXiElementaryRightEdgeIntegral]
          rw [← intervalIntegral.integral_add hprime harch,
            ← intervalIntegral.integral_add (hprime.add harch) helem]
    _ = 2 * ∫ t in (-W.rectangle.T)..W.rectangle.T,
          Complex.I *
            (h (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
              pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact hpoint t
    _ = 2 * Complex.I *
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          h (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
            pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
          rw [intervalIntegral.integral_const_mul]
          ring

/-- The vertical synthesized feature is complex-linear in its finite
coefficient vector. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_const_mul
    {n : ℕ} (a : ℂ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
        τ (fun i => a * c i) W X t u =
      a * pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
        τ c W X t u := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The top synthesized feature is complex-linear in its finite coefficient
vector. -/
theorem pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_const_mul
    {n : ℕ} (a : ℂ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
        τ (fun i => a * c i) W x v =
      a * pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
        τ c W x v := by
  unfold pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The vertical aggregate preserves coefficient scaling. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_const_mul
    {n : ℕ} (a : ℂ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ (fun i => a * c i) W X u =
      a * pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ c W X u := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
  rw [show
      (fun t : ℝ =>
        pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
          τ (fun i => a * c i) W X t u) =
      (fun t : ℝ => a *
        pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
          τ c W X t u) by
        funext t
        exact pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_const_mul
          a τ c W X t u]
  exact intervalIntegral.integral_const_mul a _

/-- The top aggregate preserves coefficient scaling. -/
theorem pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_const_mul
    {n : ℕ} (a : ℂ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
        τ (fun i => a * c i) W v =
      a * pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
        τ c W v := by
  unfold pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
  rw [show
      (fun x : ℝ =>
        pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
          τ (fun i => a * c i) W x v) =
      (fun x : ℝ => a *
        pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
          τ c W x v) by
        funext x
        exact pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_const_mul
          a τ c W x v]
  exact intervalIntegral.integral_const_mul a _

/-- The whole source feature is complex-linear in the finite coefficient
vector. -/
theorem pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature_const_mul
    {n : ℕ} (a : ℂ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
        τ (fun i => a * c i) W X u =
      a * pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
        τ c W X u := by
  unfold pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
  rw [pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_const_mul,
    pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_const_mul]
  ring

/-- The deoriented vertical source preserves coefficient scaling. -/
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalSource_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalSource
        ε τ (fun i => a * c i) W X =
      a * pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ c W X := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalSource
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  rw [show
      (fun t : ℝ =>
        (a * pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      (fun t : ℝ => a *
        (pascalCenteredXiMellinWitnessWeight ε τ c
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t)) by
        funext t
        ring]
  exact intervalIntegral.integral_const_mul a _

/-- The assembled whole source preserves coefficient scaling. -/
theorem pascalCenteredXiMellinGeneralTauWitnessWholeSource_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ (fun i => a * c i) W X =
      a * pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X := by
  unfold pascalCenteredXiMellinGeneralTauWitnessWholeSource
  rw [pascalCenteredXiMellinGeneralTauWitnessVerticalSource_const_mul,
    pascalCenteredXiMellinWitnessTopHorizontalContribution_const_mul]
  ring

/-- The whole source feature and whole source both transport the off-critical
`q.im` scalar used by the GWSS-003C witness construction. -/
theorem pascalCenteredXiMellinGeneralTauWitness_qIm_whole_source_transport
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ) (q : ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
        τ (fun i => (q.im : ℂ) * c i) W X u =
      (q.im : ℂ) * pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
        τ c W X u ∧
    pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ (fun i => (q.im : ℂ) * c i) W X =
      (q.im : ℂ) * pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ c W X := by
  constructor
  · exact pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature_const_mul
      (q.im : ℂ) τ c W X u
  · exact pascalCenteredXiMellinGeneralTauWitnessWholeSource_const_mul
      (q.im : ℂ) ε τ c W X

/-! ## F6.2: the finite ledger boundary -/

/-- The exact finite whole-source assembly once the vertical arithmetic ledger
has identified its three retained right-edge terms with the deoriented source.

The hypothesis is deliberately explicit: the currently imported finite
arithmetic API names the three terms separately, but does not yet export this
combined orientation identity for an arbitrary synthesized witness. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource_of_vertical_ledger
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hvertical :
      2 * pascalPrimePowerRightEdgeCutoffIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T X +
        2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
        2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T =
      2 * Complex.I *
        pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ c W X) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X =
      2 * Complex.I * pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ c W X := by
  unfold pascalCenteredXiFiniteArithmeticApproximant
    pascalCenteredXiMellinGeneralTauWitnessWholeSource
  rw [hvertical]
  ring_nf
  simp [Complex.I_sq]

/-- The arbitrary-weight vertical ledger specializes to the synthesized
Mellin witness without changing the finite cutoff or the source orientation.
The nonzero-`τ` hypothesis is not needed by the ledger itself; it belongs to
the preceding logarithmic-box representation. -/
theorem pascalCenteredXiMellinGeneralTauWitness_vertical_source_ledger
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    2 * pascalPrimePowerRightEdgeCutoffIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c)
        W.rectangle.σ W.rectangle.T X +
      2 * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c)
        W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c)
        W.rectangle.σ W.rectangle.T =
    2 * Complex.I *
      pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ c W X := by
  simpa only [pascalCenteredXiMellinGeneralTauWitnessVerticalSource] using
    (pascalCenteredXiMellinGeneralTau_vertical_source_ledger
      (h := pascalCenteredXiMellinWitnessWeight ε τ c)
      (pascalCenteredXiMellinWitnessWeight_differentiable hε τ c) W X)

/-- The finite arithmetic approximant has an unconditional whole-source
representation for the synthesized nonzero-`τ` witness. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X =
      2 * Complex.I * pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ c W X := by
  exact pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource_of_vertical_ledger
    ε τ c W X
    (pascalCenteredXiMellinGeneralTauWitness_vertical_source_ledger
      hε τ c W X)

/-- The finite approximant and the logarithmic whole-feature representation
compose without an `X → ∞` step. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_normalizedWholeFeatureIntegral
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X =
      2 * Complex.I *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u) := by
  rw [pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
      hε τ c W X,
    pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
      hε τ c hτ W X]

/-- The final finite representation remains compatible with the GWSS-003C
off-critical scalar `q.im`; this theorem records the two unconditional links
without asserting that the scalar vanishes or has a sign. -/
theorem pascalCenteredXiMellinGeneralTauWitness_qIm_unconditional_finite_representation
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ) (hτ : ∀ i, τ i ≠ 0)
    (q : ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (fun i => (q.im : ℂ) * c i)) W X =
      2 * Complex.I * pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ (fun i => (q.im : ℂ) * c i) W X ∧
    pascalCenteredXiMellinGeneralTauWitnessWholeSource
        ε τ (fun i => (q.im : ℂ) * c i) W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
            τ (fun i => (q.im : ℂ) * c i) W X u := by
  constructor
  · exact pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
      hε τ (fun i => (q.im : ℂ) * c i) W X
  · exact pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
      hε τ (fun i => (q.im : ℂ) * c i) hτ W X

/-- The finite whole-source ledger is also complex-linear in the witness
coefficients, provided the vertical ledger is transported with the same
scalar. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c i)) W X =
      a * pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalCenteredXiFiniteArithmeticApproximant
  have hprime :
      pascalPrimePowerRightEdgeCutoffIntegral
          (fun z => a * pascalCenteredXiMellinWitnessWeight ε τ c z)
          W.rectangle.σ W.rectangle.T X =
        a * pascalPrimePowerRightEdgeCutoffIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T X := by
    unfold pascalPrimePowerRightEdgeCutoffIntegral
    rw [show
        (fun t : ℝ =>
          pascalPrimePowerRightEdgeCutoffIntegrand
            (fun z => a * pascalCenteredXiMellinWitnessWeight ε τ c z)
            W.rectangle.σ X t) =
        (fun t : ℝ => a *
          pascalPrimePowerRightEdgeCutoffIntegrand
            (pascalCenteredXiMellinWitnessWeight ε τ c)
            W.rectangle.σ X t) by
          funext t
          unfold pascalPrimePowerRightEdgeCutoffIntegrand
          ring]
    exact intervalIntegral.integral_const_mul a _
  have harch := pascalCenteredXiMellinWitnessArchimedeanRightEdgeIntegral_const_mul
    a ε τ c W.rectangle.σ W.rectangle.T
  have helem := pascalCenteredXiMellinWitnessElementaryRightEdgeIntegral_const_mul
    a ε τ c W.rectangle.σ W.rectangle.T
  have htop := pascalCenteredXiMellinWitnessTopHorizontalContribution_const_mul
    a ε τ c W.toContourTransportWindow
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients] at harch helem htop
  rw [hprime, harch, helem, htop]
  ring

/-- The off-critical detector scalar `q.im` transports the complete finite
approximant without changing its finite window or cutoff. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_qIm_const_mul
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (q : ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (fun i => (q.im : ℂ) * c i)) W X =
      (q.im : ℂ) * pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X := by
  exact pascalCenteredXiMellinFiniteArithmeticApproximant_const_mul
    (q.im : ℂ) ε τ c W X

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
