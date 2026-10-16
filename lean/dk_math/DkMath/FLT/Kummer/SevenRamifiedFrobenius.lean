/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealGNConservation

/-!
# 分岐剰余1の七乗と、円分単元による根の正規化

具体的六次環で gamma≡1 mod lambda から gamma^7≡1 mod 7 を得る。
整数冪基底による Frobenius と同じ合同を、既存の二項係数補題と
7=lambda^6*unit から証明する。単元の七乗性の criterion は使わない。
-/

open scoped BigOperators
open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.Lib.NumberTheory

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

open SevenCyclotomicDegreeSixInt

/-- 具体的な分岐評価の零核を、向きを固定した lambda 可除性として読む。 -/
theorem ramifiedEval_eq_zero_iff_dvd (x : C) :
    ramifiedEval x = 0 ↔ ramifiedUniformizer ∣ x := by
  change x ∈ ramifiedPrime ↔ _
  rw [ramifiedPrime_eq_span_uniformizer, Ideal.mem_span_singleton]

/-- 剰余1と lambda∣gamma−1 の同値。 -/
theorem ramifiedEval_eq_one_iff_dvd (gamma : C) :
    ramifiedEval gamma = 1 ↔ ramifiedUniformizer ∣ gamma - 1 := by
  rw [← ramifiedEval_eq_zero_iff_dvd, map_sub, map_one, sub_eq_zero]

/-- 全分岐等式の一方向。内部二項係数の7を lambda^6 で割るために使う。 -/
theorem uniformizer_six_dvd_seven : ramifiedUniformizer ^ 6 ∣ (7 : C) := by
  refine ⟨ramifiedSevenUnit, ?_⟩
  simpa only [map_ofNat] using ofReal_seven_eq_uniformizer_pow_six_mul_unit

/-- 単元係数を取り除いた逆方向。lambda^6 も7で割れる。 -/
theorem seven_dvd_uniformizer_six : (7 : C) ∣ ramifiedUniformizer ^ 6 := by
  have he : (7 : C) = ramifiedUniformizer ^ 6 * ramifiedSevenUnit := by
    simpa only [map_ofNat] using ofReal_seven_eq_uniformizer_pow_six_mul_unit
  let v := ramifiedSevenUnit_isUnit.unit
  refine ⟨(↑v⁻¹ : C), ?_⟩
  rw [he, ← IsUnit.unit_spec ramifiedSevenUnit_isUnit]
  change ramifiedUniformizer ^ 6 = (ramifiedUniformizer ^ 6 * (v : C)) * (↑v⁻¹ : C)
  rw [mul_assoc]
  have hc : (v : C) * (↑v⁻¹ : C) = 1 := v.val_inv
  rw [hc, mul_one]

/-- 剰余1の七乗は mod 7 で1。実際には lambda^7 までの可除性を経由する。
根 gamma の単元性も FLT 方程式も要求しない。 -/
theorem seventh_sub_one_dvd_seven_of_residue_one {gamma : C}
    (hgamma : ramifiedEval gamma = 1) : (7 : C) ∣ gamma ^ 7 - 1 := by
  have hdeep : ramifiedUniformizer ^ 7 ∣ gamma ^ 7 - 1 :=
    prime_power_dvd_pow_sub_one_of_dvd_pred_power (by decide : Nat.Prime 7)
      uniformizer_six_dvd_seven ((ramifiedEval_eq_one_iff_dvd gamma).mp hgamma)
  exact seven_dvd_uniformizer_six.trans
    ((pow_dvd_pow ramifiedUniformizer (by decide : 6 ≤ 7)).trans hdeep)

/-- 逆方向も成立する。前章の許容単元条件 7∣t^7−1 は、ちょうど剰余 t=1。
逆方向では F_7 の Frobenius のみを使う。 -/
theorem seventh_sub_one_dvd_seven_iff_residue_one (gamma : C) :
    (7 : C) ∣ gamma ^ 7 - 1 ↔ ramifiedEval gamma = 1 := by
  constructor
  · rintro ⟨w, hw⟩
    have hh := congrArg ramifiedEval hw
    simpa only [map_sub, map_pow, map_one, map_mul, map_ofNat, ZMod.pow_card,
      show (7 : ZMod 7) = 0 from rfl, zero_mul, sub_eq_zero] using hh
  · exact seventh_sub_one_dvd_seven_of_residue_one

/-- 補正円分単元 T_i=-S_i の剰余は -i。分岐因子の符号を保存する。 -/
theorem ramifiedEval_GNRamifierTwist {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    ramifiedEval (GNRamifierTwist hi : C) = -(i : ZMod 7) := by
  change ramifiedEval (-(integralEquiv (ramifiedGeomUnit septicRoot_spec hi : _))) = _
  rw [ramifiedGeomUnit_val, map_sum]
  simp only [map_neg, map_sum, map_pow, integralEquiv_septicRoot, ramifiedEval_zeta,
    one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- 任意の非零な分岐剰余を、大域的な円分単元で持ち上げる。
環の評価の全射性だけでは単元への持ち上げにならないため、T_i を明示する。 -/
theorem exists_unit_lift_ramifiedEval (a : ZMod 7) (ha : a ≠ 0) :
    ∃ t : Cˣ, ramifiedEval (t : C) = a := by
  let i := (-a).val
  have hi : i ∈ (Finset.range 7).erase 0 := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_range.mpr (ZMod.val_lt (-a))⟩
    intro hz
    have he : (-a : ZMod 7) = 0 := by
      rw [← ZMod.natCast_zmod_val (-a), show (-a).val = 0 from hz]
      rfl
    exact ha (neg_eq_zero.mp he)
  refine ⟨GNRamifierTwist hi, ?_⟩
  rw [ramifiedEval_GNRamifierTwist]
  change -(((-a).val : ℕ) : ZMod 7) = a
  rw [ZMod.natCast_zmod_val, neg_neg]

/-- 非分岐な根を単元倍で剰余1に選び直す。元の根との関係を同じ t で保持する。 -/
theorem exists_root_residue_normalizer (beta : C) (hbeta : ¬ ramifiedUniformizer ∣ beta) :
    ∃ t : Cˣ, ramifiedEval ((t : C) * beta) = 1 := by
  have hb : ramifiedEval beta ≠ 0 := fun hz => hbeta ((ramifiedEval_eq_zero_iff_dvd beta).mp hz)
  obtain ⟨t, ht⟩ := exists_unit_lift_ramifiedEval (ramifiedEval beta)⁻¹ (inv_ne_zero hb)
  exact ⟨t, by rw [map_mul, ht, inv_mul_cancel₀ hb]⟩

end

end DkMath.FLT.Kummer.SevenRealGN
