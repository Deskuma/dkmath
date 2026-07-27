/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.SquareTailGapIdentity
import DkMath.ABC.GNQualityExcessBridge

#print "file: DkMath.ABC.ABCEpsilonIdentity"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Intrinsic ABC epsilon identities

This module identifies the multiplicity discarded by `rad` with the exact
square-tail quotient.  It is the first bridge from the existing GN valuation
accounting to the intrinsic epsilon coordinate of an ABC triple.
-/

namespace DkMath.ABC

/--
The logarithmic multiplicity discarded by the radical is exactly the logarithm
of the square-tail quotient.
-/
theorem valuationExcess_eq_log_sqTail
    {m : ℕ} (hm : m ≠ 0) :
    valuationExcess m = Real.log (sqTail m : ℝ) := by
  have hlog := log_eq_log_rad_add_valuationExcess hm
  have hdecomp := nat_eq_sqTail_mul_rad_real m hm
  have hsqTail : (sqTail m : ℝ) ≠ 0 := by
    intro hzero
    have hsqTailNat : sqTail m = 0 := by
      exact_mod_cast hzero
    apply hm
    calc
      m = sqTail m * rad m := nat_eq_sqTail_mul_rad m hm
      _ = 0 := by simp [hsqTailNat]
  have hrad : (rad m : ℝ) ≠ 0 := by
    exact_mod_cast rad_ne_zero m
  have hmul :
      Real.log (m : ℝ) =
        Real.log (sqTail m : ℝ) + Real.log (rad m : ℝ) := by
    rw [hdecomp, Real.log_mul hsqTail hrad]
  linarith

/--
The square-tail debt of an ABC triple is exactly its output valuation excess
minus the logarithmic radical support already paid by the two inputs.
-/
theorem Triple.squareTailDebt_eq_valuationExcess_sub_log_rad_ab
    (T : Triple)
    (hc : T.c ≠ 0) :
    T.squareTailDebt =
      valuationExcess T.c - Real.log (rad (T.a * T.b) : ℝ) := by
  simpa [Triple.squareTailDebt] using congrArg
    (fun x : ℝ => x - Real.log (rad (T.a * T.b) : ℝ))
    (valuationExcess_eq_log_sqTail hc).symm

/--
The ordinary ABC gap is exactly the output valuation excess remaining after
subtracting the radical support supplied by the two input coordinates.
-/
theorem Triple.abcGap_eq_valuationExcess_sub_log_rad_ab
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcGap =
      valuationExcess T.c - Real.log (rad (T.a * T.b) : ℝ) := by
  have hc : T.c ≠ 0 := by
    intro hc0
    have hab0 : T.a + T.b = 0 := by
      simpa [hc0] using T.hsum
    exact (Nat.ne_of_gt ha) (Nat.add_eq_zero_iff.mp hab0).1
  calc
    T.abcGap = T.squareTailDebt := T.abcGap_eq_squareTailDebt ha hb
    _ = valuationExcess T.c - Real.log (rad (T.a * T.b) : ℝ) :=
      T.squareTailDebt_eq_valuationExcess_sub_log_rad_ab hc

/-- The logarithmic scale of the complete ABC radical. -/
noncomputable def Triple.radLog (T : Triple) : ℝ :=
  Real.log (rad (T.a * T.b * T.c) : ℝ)

/--
The signed intrinsic epsilon coordinate of an ABC triple: its exact logarithmic
ABC gap normalized by the logarithmic scale of the complete radical.
-/
noncomputable def Triple.abcEpsilon (T : Triple) : ℝ :=
  T.abcGap / T.radLog

/-- The intrinsic epsilon coordinate reconstructs the exact ABC gap. -/
theorem Triple.abcGap_eq_abcEpsilon_mul_radLog
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcGap = T.abcEpsilon * T.radLog := by
  have hrad : T.radLog ≠ 0 := by
    exact ne_of_gt (by
      simpa [Triple.radLog] using T.log_rad_abc_pos ha hb)
  simpa [Triple.abcEpsilon] using
    (div_mul_cancel₀ T.abcGap hrad).symm

/--
The intrinsic epsilon coordinate is the normalized difference between output
valuation multiplicity and the radical support supplied by the two inputs.
-/
theorem Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcEpsilon =
      (valuationExcess T.c - Real.log (rad (T.a * T.b) : ℝ)) /
        Real.log (rad (T.a * T.b * T.c) : ℝ) := by
  simp only [Triple.abcEpsilon, Triple.radLog]
  rw [T.abcGap_eq_valuationExcess_sub_log_rad_ab ha hb]

/-- ABC quality is exactly one plus the signed intrinsic epsilon coordinate. -/
theorem Triple.quality_eq_one_add_abcEpsilon
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    quality T = 1 + T.abcEpsilon := by
  have hrad :
      Real.log (rad (T.a * T.b * T.c) : ℝ) ≠ 0 :=
    ne_of_gt (T.log_rad_abc_pos ha hb)
  simp only [quality, Triple.abcEpsilon, Triple.abcGap, Triple.radLog]
  field_simp [hrad]
  ring

/--
A quality threshold above `1 + ε` is exactly the statement that the external
threshold `ε` lies below the triple's intrinsic epsilon coordinate.
-/
theorem Triple.one_add_lt_quality_iff_lt_abcEpsilon
    (T : Triple)
    (ε : ℝ)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    1 + ε < quality T ↔ ε < T.abcEpsilon := by
  rw [T.quality_eq_one_add_abcEpsilon ha hb]
  exact add_lt_add_iff_left 1

/--
An external threshold below the intrinsic epsilon coordinate forces the
corresponding affine GN valuation-excess lower bound.
-/
theorem Triple.GNValuationExcess_gt_of_abcEpsilon_gt_pred_affine
    (T : Triple) {n : ℕ} {ε σ C : ℝ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hε : ε < T.abcEpsilon)
    (hsupport : GNSupportBudgetAffine T n σ C) :
    ((((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
          Real.log (rad (T.a * T.b * T.c) : ℝ)) - C <
      GNValuationExcess n T.a T.b := by
  have hquality : 1 + ε < quality T :=
    (T.one_add_lt_quality_iff_lt_abcEpsilon ε ha hb).2 hε
  exact T.GNValuationExcess_gt_of_quality_gt_pred_affine
    hn ha hb hquality hsupport

/--
Pure support-budget specialization of the intrinsic-epsilon GN excess bridge.
-/
theorem Triple.GNValuationExcess_gt_of_abcEpsilon_gt_pred
    (T : Triple) {n : ℕ} {ε σ : ℝ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hε : ε < T.abcEpsilon)
    (hsupport : GNSupportBudget T n σ) :
    (((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
        Real.log (rad (T.a * T.b * T.c) : ℝ) <
      GNValuationExcess n T.a T.b := by
  simpa using T.GNValuationExcess_gt_of_abcEpsilon_gt_pred_affine
    hn ha hb hε hsupport.toAffine

/--
An affine upper bound for the logarithmic ABC gap normalizes to an upper bound
for the intrinsic epsilon coordinate.
-/
theorem Triple.abcEpsilon_le_add_div_of_abcGap_le_affine
    (T : Triple) {ε C : ℝ}
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hgap : T.abcGap ≤ ε * T.radLog + C) :
    T.abcEpsilon ≤ ε + C / T.radLog := by
  have hrad : 0 < T.radLog := by
    simpa [Triple.radLog] using T.log_rad_abc_pos ha hb
  rw [Triple.abcEpsilon]
  apply (div_le_iff₀ hrad).2
  calc
    T.abcGap ≤ ε * T.radLog + C := hgap
    _ = (ε + C / T.radLog) * T.radLog := by
      rw [add_mul, div_mul_cancel₀ C (ne_of_gt hrad)]

/--
A natural ABC bound yields the corresponding affine upper bound for the
logarithmic ABC gap.
-/
theorem Triple.abcGap_le_mul_radLog_add_log_of_abc_bound
    (T : Triple) {ε K : ℝ}
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hK : 0 < K)
    (hbound :
      (T.c : ℝ) ≤
        K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε)) :
    T.abcGap ≤ ε * T.radLog + Real.log K := by
  have hcNat : 0 < T.c := by
    rw [← T.hsum]
    omega
  have hc : 0 < (T.c : ℝ) := by
    exact_mod_cast hcNat
  have habc : 0 < T.a * T.b * T.c :=
    Nat.mul_pos (Nat.mul_pos ha hb) hcNat
  have hrad :
      0 < (rad (T.a * T.b * T.c) : ℝ) := by
    exact_mod_cast rad_pos habc
  have hrpow :
      0 < (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) :=
    Real.rpow_pos_of_pos hrad _
  have hlog := Real.log_le_log hc hbound
  rw [Real.log_mul hK.ne' hrpow.ne',
    Real.log_rpow hrad] at hlog
  simp only [Triple.abcGap, Triple.radLog]
  linarith

/--
A natural ABC bound directly yields the normalized intrinsic-epsilon upper
bound, with the multiplicative constant appearing as a vanishing log correction.
-/
theorem Triple.abcEpsilon_le_add_log_div_radLog_of_abc_bound
    (T : Triple) {ε K : ℝ}
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hK : 0 < K)
    (hbound :
      (T.c : ℝ) ≤
        K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε)) :
    T.abcEpsilon ≤ ε + Real.log K / T.radLog := by
  apply T.abcEpsilon_le_add_div_of_abcGap_le_affine ha hb
  exact T.abcGap_le_mul_radLog_add_log_of_abc_bound ha hb hK hbound

/--
Along any family of ABC triples whose radical-log scale tends to infinity, the
fixed multiplicative constant contributes a vanishing intrinsic-epsilon term.
-/
theorem tendsto_log_div_radLog_zero
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    (K : ℝ)
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop) :
    Filter.Tendsto
      (fun i => Real.log K / (T i).radLog) l (nhds 0) := by
  exact tendsto_const_nhds.div_atTop hrad

/--
Along a family satisfying a fixed ABC bound and with radical-log scale tending
to infinity, the intrinsic epsilon coordinate is eventually at most `ε + η`
for every positive tolerance `η`.
-/
theorem eventually_abcEpsilon_le_add_of_abc_bound
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    (ε K η : ℝ)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hK : 0 < K)
    (hbound :
      ∀ᶠ i in l,
        ((T i).c : ℝ) ≤
          K * (rad ((T i).a * (T i).b * (T i).c) : ℝ) ^ (1 + ε))
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hη : 0 < η) :
    ∀ᶠ i in l, (T i).abcEpsilon ≤ ε + η := by
  have hcorr := tendsto_log_div_radLog_zero T K hrad
  have hsmall :
      ∀ᶠ i in l, Real.log K / (T i).radLog < η :=
    (tendsto_order.1 hcorr).2 η hη
  filter_upwards [ha, hb, hbound, hsmall] with i hai hbi hboundi hsmalli
  exact le_trans
    ((T i).abcEpsilon_le_add_log_div_radLog_of_abc_bound
      hai hbi hK hboundi)
    (add_le_add_right (le_of_lt hsmalli) ε)

/--
Every strict threshold above the external exponent is eventually above the
intrinsic epsilon coordinate along the same large-radical family.
-/
theorem eventually_abcEpsilon_lt_of_abc_bound
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    (ε K δ : ℝ)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hK : 0 < K)
    (hbound :
      ∀ᶠ i in l,
        ((T i).c : ℝ) ≤
          K * (rad ((T i).a * (T i).b * (T i).c) : ℝ) ^ (1 + ε))
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hεδ : ε < δ) :
    ∀ᶠ i in l, (T i).abcEpsilon < δ := by
  have hη : 0 < (δ - ε) / 2 := by
    exact div_pos (sub_pos.mpr hεδ) (by norm_num)
  have hle := eventually_abcEpsilon_le_add_of_abc_bound
    T ε K ((δ - ε) / 2) ha hb hK hbound hrad hη
  have hmid : ε + (δ - ε) / 2 < δ := by
    linarith
  filter_upwards [hle] with i hi
  exact lt_of_le_of_lt hi hmid

/--
No strict threshold above the external exponent can be reached frequently by
intrinsic epsilon along the same large-radical family.
-/
theorem not_frequently_le_abcEpsilon_of_abc_bound
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    (ε K δ : ℝ)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hK : 0 < K)
    (hbound :
      ∀ᶠ i in l,
        ((T i).c : ℝ) ≤
          K * (rad ((T i).a * (T i).b * (T i).c) : ℝ) ^ (1 + ε))
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hεδ : ε < δ) :
    ¬ ∃ᶠ i in l, δ ≤ (T i).abcEpsilon := by
  intro hfreq
  apply hfreq
  have hlt := eventually_abcEpsilon_lt_of_abc_bound
    T ε K δ ha hb hK hbound hrad hεδ
  filter_upwards [hlt] with i hi
  exact not_le.mpr hi

/--
The same large-radical ABC family has quality eventually below every strict
threshold `1 + δ` with `ε < δ`.
-/
theorem eventually_quality_lt_one_add_of_abc_bound
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    (ε K δ : ℝ)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hK : 0 < K)
    (hbound :
      ∀ᶠ i in l,
        ((T i).c : ℝ) ≤
          K * (rad ((T i).a * (T i).b * (T i).c) : ℝ) ^ (1 + ε))
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hεδ : ε < δ) :
    ∀ᶠ i in l, quality (T i) < 1 + δ := by
  have hεlt := eventually_abcEpsilon_lt_of_abc_bound
    T ε K δ ha hb hK hbound hrad hεδ
  filter_upwards [ha, hb, hεlt] with i hai hbi hi
  rw [(T i).quality_eq_one_add_abcEpsilon hai hbi]
  exact add_lt_add_right hi 1

end DkMath.ABC
