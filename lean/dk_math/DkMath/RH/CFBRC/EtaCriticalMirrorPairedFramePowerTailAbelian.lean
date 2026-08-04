/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePowerTailAbelian"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter Set MeasureTheory
open scoped Topology

/-- Shifted model tail with exponent `alpha + 1`. -/
noncomputable def shiftedRpowModelTail
    (alpha : ℝ) (K : ℕ) : ℝ :=
  ∑' n : ℕ,
    (((n + K + 1 : ℕ) : ℝ) ^ (-alpha - 1))

/-- The unshifted successor power model is summable for positive `alpha`. -/
private theorem summable_successor_rpow_model
    {alpha : ℝ} (halpha : 0 < alpha) :
    Summable
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1))) := by
  have hp : 1 < alpha + 1 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(alpha + 1))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hshift := (summable_nat_add_iff 1).2 hbase
  simpa [show -alpha - 1 = -(alpha + 1) by ring] using hshift

/-- Every shifted power-model tail is summable. -/
theorem summable_shiftedRpowModelTail
    {alpha : ℝ} (halpha : 0 < alpha) (K : ℕ) :
    Summable
      (fun n : ℕ =>
        (((n + K + 1 : ℕ) : ℝ) ^ (-alpha - 1))) := by
  have h := (summable_nat_add_iff K).2
    (summable_successor_rpow_model halpha)
  simpa [Nat.add_assoc] using h

/-- Integral-test lower bound for the shifted power-model tail. -/
theorem shifted_rpow_model_tail_lower
    {alpha : ℝ} (halpha : 0 < alpha) (K : ℕ) :
    ((((K + 1 : ℕ) : ℝ) ^ (-alpha)) / alpha) ≤
      shiftedRpowModelTail alpha K := by
  let N : ℕ := K + 1
  have hNpos : 0 < (N : ℝ) := by
    dsimp [N]
    positivity
  have hExpLt : -alpha - 1 < -1 := by linarith
  have hExpNonpos : -alpha - 1 ≤ 0 := by linarith
  have hanti :
      AntitoneOn
        (fun x : ℝ => x ^ (-alpha - 1))
        (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hExpNonpos
        (hNpos.trans_le hx) (hNpos.trans_le hy) hxy
  have hsum :
      Summable (fun n : ℕ => (n : ℝ) ^ (-alpha - 1)) := by
    have hp : 1 < alpha + 1 := by linarith
    have hbase :
        Summable (fun n : ℕ => (n : ℝ) ^ (-(alpha + 1))) := by
      simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
        (Real.summable_one_div_nat_rpow.2 hp)
    simpa [show -alpha - 1 = -(alpha + 1) by ring] using hbase
  have hnonneg :
      ∀ x ∈ Ioi (N : ℝ), 0 ≤ x ^ (-alpha - 1) := by
    intro x hx
    exact Real.rpow_nonneg (hNpos.trans hx).le _
  have hlower :=
    hanti.integral_le_tsum_comp_add N hsum hnonneg
  have hintegral :
      (∫ x : ℝ in Ioi (N : ℝ), x ^ (-alpha - 1)) =
        ((N : ℝ) ^ (-alpha)) / alpha := by
    rw [integral_Ioi_rpow_of_lt hExpLt hNpos]
    rw [show -alpha - 1 + 1 = -alpha by ring]
    field_simp [ne_of_gt halpha]
  rw [hintegral] at hlower
  unfold shiftedRpowModelTail
  simpa [N, Nat.add_assoc] using hlower

/-- Positive-base division law for real powers. -/
private theorem div_rpow_pos_powerTail
    {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b) ^ p = a ^ p / b ^ p := by
  rw [div_eq_mul_inv]
  rw [Real.mul_rpow ha.le (inv_nonneg.mpr hb.le)]
  rw [Real.inv_rpow hb.le]
  rw [← div_eq_mul_inv]

/-- The normalized shifted model tail converges to the integral constant `1 / alpha`. -/
theorem normalized_shiftedRpowModelTail_tendsto_inv
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K)
      atTop (nhds ((1 : ℝ) / alpha)) := by
  have hratio :
      Tendsto
        (fun K : ℕ => (K : ℝ) / ((K : ℝ) + 1))
        atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hratioPow :=
    hratio.rpow_const (p := alpha) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hlowerTendsto :
      Tendsto
        (fun K : ℕ =>
          (((K : ℝ) / ((K : ℝ) + 1)) ^ alpha) / alpha)
        atTop (nhds ((1 : ℝ) / alpha)) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ) / alpha)
          atTop (nhds ((1 : ℝ) / alpha))).mul hratioPow
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hlower :
      ∀ᶠ K : ℕ in atTop,
        (((K : ℝ) / ((K : ℝ) + 1)) ^ alpha) / alpha ≤
          ((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
    have hK1pos : 0 < (((K + 1 : ℕ) : ℝ)) := by positivity
    have htail := shifted_rpow_model_tail_lower halpha K
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ alpha :=
      (Real.rpow_pos_of_pos hKpos _).le
    have heq :
        ((K : ℝ) ^ alpha) *
            (((((K + 1 : ℕ) : ℝ) ^ (-alpha)) / alpha)) =
          (((K : ℝ) / ((K : ℝ) + 1)) ^ alpha) / alpha := by
      rw [div_rpow_pos_powerTail hKpos hK1pos]
      rw [Real.rpow_neg hK1pos.le]
      norm_num [Nat.cast_add]
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left htail hscaleNonneg
  have hupper :
      ∀ᶠ K : ℕ in atTop,
        ((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K ≤
          (1 : ℝ) / alpha := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
    have htail := shifted_rpow_tail_le halpha hK
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ alpha :=
      (Real.rpow_pos_of_pos hKpos _).le
    have hcancel :
        ((K : ℝ) ^ alpha) * ((K : ℝ) ^ (-alpha)) = 1 := by
      rw [← Real.rpow_add hKpos]
      simp
    calc
      ((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K ≤
          ((K : ℝ) ^ alpha) *
            (((K : ℝ) ^ (-alpha)) / alpha) :=
        mul_le_mul_of_nonneg_left htail hscaleNonneg
      _ = (1 : ℝ) / alpha := by
        rw [show
          ((K : ℝ) ^ alpha) *
              (((K : ℝ) ^ (-alpha)) / alpha) =
            ((((K : ℝ) ^ alpha) * ((K : ℝ) ^ (-alpha))) / alpha) by ring]
        rw [hcancel]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowerTendsto tendsto_const_nhds hlower hupper

/-- Tail of a real sequence beginning at index `K`. -/
noncomputable def realSequenceTail
    (a : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑' n : ℕ, a (n + K)

/-- Residual after subtracting the power-law main term. -/
noncomputable def powerTailResidual
    (a : ℕ → ℝ) (alpha D : ℝ) (n : ℕ) : ℝ :=
  a n - D * (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1))

/-- The model power times its inverse power is one. -/
private theorem successor_rpow_cancel
    (alpha : ℝ) (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
        (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1)) = 1 := by
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [← Real.rpow_add hn]
  simp

/-- The scaled residual tends to zero whenever the scaled original term tends to `D`. -/
theorem powerTailResidual_scaled_tendsto_zero
    {a : ℕ → ℝ} {alpha D : ℝ}
    (hterm : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n)
      atTop (nhds D)) :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
          powerTailResidual a alpha D n)
      atTop (nhds 0) := by
  have hsub := hterm.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => D) atTop (nhds D))
  refine hsub.congr' (Eventually.of_forall fun n => ?_)
  unfold powerTailResidual
  have hcancel := successor_rpow_cancel alpha n
  calc
    (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
        (a n - D * (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1))) =
      (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n -
        D *
          ((((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
            (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1))) := by ring
    _ = (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n - D := by
      rw [hcancel, mul_one]

/-- Exact reconstruction of a residual from its scaled form. -/
private theorem powerTailResidual_eq_inverse_mul_scaled
    (a : ℕ → ℝ) (alpha D : ℝ) (n : ℕ) :
    powerTailResidual a alpha D n =
      (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1)) *
        ((((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
          powerTailResidual a alpha D n) := by
  have hcancel := successor_rpow_cancel alpha n
  calc
    powerTailResidual a alpha D n =
      1 * powerTailResidual a alpha D n := by ring
    _ =
      ((((n + 1 : ℕ) : ℝ) ^ (-alpha - 1)) *
          (((n + 1 : ℕ) : ℝ) ^ (alpha + 1))) *
        powerTailResidual a alpha D n := by
      rw [show
        (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1)) *
            (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) = 1 by
          nlinarith [hcancel]]
    _ = _ := by ring

/-- Eventual pointwise residual bound extracted from a scaled zero limit. -/
theorem eventually_abs_powerTailResidual_le
    {a : ℕ → ℝ} {alpha D : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
          powerTailResidual a alpha D n)
      atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |powerTailResidual a alpha D n| ≤
        epsilon * (((n + 1 : ℕ) : ℝ) ^ (-alpha - 1)) := by
  rw [Metric.tendsto_atTop] at hscaled
  obtain ⟨N, hN⟩ := hscaled epsilon hepsilon
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero] at hsmall
  rw [powerTailResidual_eq_inverse_mul_scaled]
  rw [abs_mul]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_left (le_of_lt hsmall)
    (Real.rpow_nonneg (by positivity) _)

/-- The residual sequence is summable if the original sequence is summable. -/
theorem summable_powerTailResidual
    {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha) (ha : Summable a) :
    Summable (powerTailResidual a alpha D) := by
  have hmodel := (summable_successor_rpow_model halpha).mul_left D
  exact ha.sub hmodel

/-- A scaled-zero residual has a normalized tail converging to zero. -/
theorem normalized_powerTailResidual_tail_tendsto_zero
    {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha)
    (hresSum : Summable (powerTailResidual a alpha D))
    (hscaled : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
          powerTailResidual a alpha D n)
      atTop (nhds 0)) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ alpha) *
          realSequenceTail (powerTailResidual a alpha D) K)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro delta hdelta
  let epsilon : ℝ := delta * alpha / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hpointEventually :=
    eventually_abs_powerTailResidual_le hscaled hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpointEventually
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKN : N ≤ K := le_trans (le_max_left _ _) hK
  have hKone : 1 ≤ K := le_trans (le_max_right _ _) hK
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hKone
  have hmodelShift := summable_shiftedRpowModelTail halpha K
  have hmajorant := hmodelShift.mul_left epsilon
  have hresShift :
      Summable
        (fun n : ℕ => powerTailResidual a alpha D (n + K)) :=
    (summable_nat_add_iff K).2 hresSum
  have htailNorm :
      |realSequenceTail (powerTailResidual a alpha D) K| ≤
        ∑' n : ℕ,
          epsilon *
            (((n + K + 1 : ℕ) : ℝ) ^ (-alpha - 1)) := by
    unfold realSequenceTail
    exact
      tsum_of_norm_bounded hmajorant.hasSum
        (fun n => by
          rw [Real.norm_eq_abs]
          have hn : N ≤ n + K := by omega
          simpa [Nat.add_assoc] using hN (n + K) hn)
  have hfactor :
      (∑' n : ℕ,
        epsilon *
          (((n + K + 1 : ℕ) : ℝ) ^ (-alpha - 1))) =
        epsilon * shiftedRpowModelTail alpha K := by
    unfold shiftedRpowModelTail
    exact (hmodelShift.hasSum.mul_left epsilon).tsum_eq
  rw [hfactor] at htailNorm
  have hmodelUpper := shifted_rpow_tail_le halpha hKone
  have hscaleNonneg : 0 ≤ (K : ℝ) ^ alpha :=
    (Real.rpow_pos_of_pos hKpos _).le
  have hcancel :
      ((K : ℝ) ^ alpha) * ((K : ℝ) ^ (-alpha)) = 1 := by
    rw [← Real.rpow_add hKpos]
    simp
  have hbound :
      |((K : ℝ) ^ alpha) *
          realSequenceTail (powerTailResidual a alpha D) K| ≤
        epsilon / alpha := by
    rw [abs_mul, abs_of_nonneg hscaleNonneg]
    calc
      ((K : ℝ) ^ alpha) *
          |realSequenceTail (powerTailResidual a alpha D) K| ≤
        ((K : ℝ) ^ alpha) *
          (epsilon * shiftedRpowModelTail alpha K) :=
        mul_le_mul_of_nonneg_left htailNorm hscaleNonneg
      _ ≤ ((K : ℝ) ^ alpha) *
          (epsilon * (((K : ℝ) ^ (-alpha)) / alpha)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmodelUpper hepsilon.le)
          hscaleNonneg
      _ = epsilon / alpha := by
        rw [show
          ((K : ℝ) ^ alpha) *
              (epsilon * (((K : ℝ) ^ (-alpha)) / alpha)) =
            epsilon *
              ((((K : ℝ) ^ alpha) * ((K : ℝ) ^ (-alpha))) / alpha) by ring]
        rw [hcancel]
  rw [Real.dist_eq, sub_zero]
  have heq : epsilon / alpha = delta / 2 := by
    dsimp [epsilon]
    field_simp [ne_of_gt halpha]
    ring
  rw [heq] at hbound
  exact hbound.trans_lt (by linarith)

/-- Exact decomposition of a sequence tail into its power main term and residual. -/
theorem realSequenceTail_eq_model_add_residual
    {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha) (ha : Summable a) (K : ℕ) :
    realSequenceTail a K =
      D * shiftedRpowModelTail alpha K +
        realSequenceTail (powerTailResidual a alpha D) K := by
  have hmodelShift := summable_shiftedRpowModelTail halpha K
  have hresSum := summable_powerTailResidual halpha ha
  have hresShift :
      Summable
        (fun n : ℕ => powerTailResidual a alpha D (n + K)) :=
    (summable_nat_add_iff K).2 hresSum
  have hsum := (hmodelShift.mul_left D).hasSum.add hresShift.hasSum
  unfold realSequenceTail shiftedRpowModelTail
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro n
  unfold powerTailResidual
  ring

/--
Power-tail Abelian theorem for summable real sequences.

No monotonicity is assumed: a scaled pointwise limit and summability suffice.
-/
theorem normalized_realSequenceTail_tendsto
    {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha)
    (ha : Summable a)
    (hterm : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n)
      atTop (nhds D)) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ alpha) * realSequenceTail a K)
      atTop (nhds (D / alpha)) := by
  have hmodel := normalized_shiftedRpowModelTail_tendsto_inv halpha
  have hmain :
      Tendsto
        (fun K : ℕ =>
          D * (((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K))
        atTop (nhds (D / alpha)) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => D) atTop (nhds D)).mul hmodel
    simpa [div_eq_mul_inv, mul_assoc] using h
  have hresScaled := powerTailResidual_scaled_tendsto_zero hterm
  have hresSum := summable_powerTailResidual halpha ha
  have hres :=
    normalized_powerTailResidual_tail_tendsto_zero
      halpha hresSum hresScaled
  have hsum := hmain.add hres
  refine hsum.congr' (Eventually.of_forall fun K => ?_)
  rw [realSequenceTail_eq_model_add_residual halpha ha K]
  ring

end DkMath.RH.CFBRCProjection
