/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideMonotonicityStrengthAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit
import Mathlib.Tactic

/-!
# CS21: good finite cutoffs and cofinal upper anchors

This module weakens the CS19/CS20 universal sign route.  It packages the
exact absolute defect-tail error, the fixed-ε eventual tail tolerance, and a
cofinal finite upper-anchor contract.  The source estimate needed to
instantiate that contract remains a named frontier.

No universal tail sign, monotonicity, terminal ceiling, infinite exchange,
endpoint sign, fixed-defect RH argument, or RH conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

local notation "DεX" => pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
local notation "Dε∞" => pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
local notation "PεX" => pascalCenteredXiPrimeSideFiniteTailProjection

/-! ## CS21-A: exact absolute residual adapters -/

theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_le_approximant_add_abs_tail
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Dε∞ ε W ≤
      DεX ε W X + (2 / Real.pi) * |PεX ε W X| := by
  have hEq := pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
    hε W X
  have hc : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (neg_le_abs (PεX ε W X)) hc
  nlinarith [hEq, hmul]

theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_abs_eq_abs_tail
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    |DεX ε W X - Dε∞ ε W| =
      (2 / Real.pi) * |PεX ε W X| := by
  have hEq := pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
    hε W X
  rw [hEq, abs_mul, abs_of_pos (by positivity : 0 < (2 / Real.pi : ℝ))]

/-! ## CS21-B: fixed-ε eventual absolute smallness -/

theorem eventually_pascalCenteredXiPrimeSideFiniteTailProjection_abs_le
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∀ᶠ X : ℕ in atTop, |PεX ε W X| ≤ δ := by
  have hconv := pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero hε W
  have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds (0 : ℝ) hδ
  have hev : ∀ᶠ X : ℕ in atTop,
      PεX ε W X ∈ Metric.ball (0 : ℝ) δ := hconv.eventually hball
  exact hev.mono (by
    intro X hX
    have hlt : |PεX ε W X| < δ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hX
    exact hlt.le)

theorem eventually_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_abs_le
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∀ᶠ X : ℕ in atTop,
      |DεX ε W X - Dε∞ ε W| ≤ (2 / Real.pi) * δ := by
  have htail := eventually_pascalCenteredXiPrimeSideFiniteTailProjection_abs_le
    hε hδ W
  filter_upwards [htail] with X hX
  rw [pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_abs_eq_abs_tail
    hε W X]
  exact mul_le_mul_of_nonneg_left hX (by positivity)

/-! ## CS21-C: cofinal finite-cutoff upper-anchor contract -/

def PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (r : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    DεX ε W X ≤ r + δ

/-! ## CS21-D: exact fixed-ε strength classification -/

theorem pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_endpoint_le
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt ε W r ↔
      Dε∞ ε W ≤ r := by
  constructor
  · intro hanchor
    by_contra hnot
    have hgap : r < Dε∞ ε W := lt_of_not_ge hnot
    let δ : ℝ := (Dε∞ ε W - r) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hbelow : r + δ < Dε∞ ε W := by
      dsimp [δ]
      linarith
    have hev :=
      (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant hε W)
        (Ioi_mem_nhds hbelow)
    rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
    rcases hanchor δ hδ N with ⟨X, hNX, hupper⟩
    have hlower := hN X hNX
    change r + δ < DεX ε W X at hlower
    linarith
  · intro hend δ hδ N
    have hev :=
      (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant hε W)
        (Iio_mem_nhds (by linarith : Dε∞ ε W < Dε∞ ε W + δ))
    rcases (eventually_atTop.1 hev) with ⟨M, hM⟩
    let X : ℕ := max N M
    have hNX : N ≤ X := le_max_left _ _
    have hMX : M ≤ X := le_max_right _ _
    have hupper : DεX ε W X < Dε∞ ε W + δ := hM X hMX
    refine ⟨X, hNX, ?_⟩
    have hbound : Dε∞ ε W + δ ≤ r + δ := by
      nlinarith [hend]
    exact (lt_of_lt_of_le hupper hbound).le

/-! ## CS21-E: one good finite cutoff and endpoint adapter -/

structure PascalCenteredXiPrimeSideGoodFiniteCutoff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (r δ : ℝ) where
  X : ℕ
  approximant_upper : DεX ε W X ≤ r
  tail_abs_le : |PεX ε W X| ≤ δ

theorem pascalCenteredXiPrimeSideGoodFiniteCutoff_endpoint_le
    {ε r δ : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hgood : PascalCenteredXiPrimeSideGoodFiniteCutoff ε W r δ) :
    Dε∞ ε W ≤ r + (2 / Real.pi) * δ := by
  have hres := pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_le_approximant_add_abs_tail
    hε W hgood.X
  have hmul : (2 / Real.pi : ℝ) * |PεX ε W hgood.X| ≤
      (2 / Real.pi) * δ :=
    mul_le_mul_of_nonneg_left hgood.tail_abs_le (by positivity)
  calc
    Dε∞ ε W ≤ DεX ε W hgood.X + (2 / Real.pi) * |PεX ε W hgood.X| := hres
    _ ≤ r + (2 / Real.pi) * δ := by
      linarith [hgood.approximant_upper, hmul]

/-! ## CS21-F: vanishing good-cutoff family -/

structure PascalCenteredXiPrimeSideVanishingGoodCutoffFamily
    (W : PascalCenteredXiResidueTransportWindow) where
  r : ℝ → ℝ
  δ : ℝ → ℝ
  cutoff : ℝ → ℕ
  r_tendsto_zero : Tendsto r (𝓝[>] 0) (nhds 0)
  δ_tendsto_zero : Tendsto δ (𝓝[>] 0) (nhds 0)
  positive_epsilon : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε
  approximant_upper : ∀ᶠ ε : ℝ in 𝓝[>] 0,
    DεX ε W (cutoff ε) ≤ r ε
  tail_abs_le : ∀ᶠ ε : ℝ in 𝓝[>] 0,
    |PεX ε W (cutoff ε)| ≤ δ ε

theorem pascalCenteredXiPrimeSideVanishingGoodCutoffFamily_implies_upperEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (H : PascalCenteredXiPrimeSideVanishingGoodCutoffFamily W) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W := by
  let c : ℝ := 2 / Real.pi
  refine ⟨fun ε => H.r ε + c * H.δ ε, ?_, ?_⟩
  · have hc : Tendsto (fun _ : ℝ => c) (𝓝[>] 0) (nhds c) :=
      tendsto_const_nhds
    have hscaled : Tendsto (fun ε : ℝ => c * H.δ ε)
        (𝓝[>] 0) (nhds (c * 0)) := hc.mul H.δ_tendsto_zero
    simpa [c] using H.r_tendsto_zero.add hscaled
  · filter_upwards [H.positive_epsilon, H.approximant_upper, H.tail_abs_le]
      with ε hε hupper htail
    have hgood : PascalCenteredXiPrimeSideGoodFiniteCutoff ε W (H.r ε) (H.δ ε) :=
      ⟨H.cutoff ε, hupper, htail⟩
    have hbound := pascalCenteredXiPrimeSideGoodFiniteCutoff_endpoint_le
      hε W hgood
    simpa [c] using hbound

/-! ## CS21-H: explicit finite source ledger -/

theorem pascalCenteredXiPrimeSideGoodCutoff_source_ledger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X =
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        (((2 * Real.pi * Complex.I)⁻¹ *
          (2 * (∑ n ∈ Finset.range (X + 1),
            ∫ t in (-W.rectangle.T)..W.rectangle.T,
              (pascalCenteredXiMellinSecondDifferenceWeight ε 0
                (pascalOrdinaryToCentered
                  (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
                ((ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((n : ℂ) ^
                    (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
                Complex.I)) +
          2 * pascalXiArchimedeanRightEdgeIntegral
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ W.rectangle.T +
          2 * pascalXiElementaryRightEdgeIntegral
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ W.rectangle.T +
          2 * pascalCenteredXiTopHorizontalContribution
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.toContourTransportWindow)).re) := by
  exact pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface
    hε W X

/-! ## CS21-I: source frontier -/

inductive PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorGap : Prop
  | noIndependentCofinalFiniteUpperAnchorProvider

end DkMath.RH.CFBRCProjection
