/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenDescentPowers
import DkMath.FLT.Kummer.SevenKummerUnit

#print "file: DkMath.FLT.Kummer.SevenDescentUnits"

/-! # FLT7教科書：新しい二項の係数比
必要なのは全単元の七乗性ではなく、再構成した二項の係数比の七乗性である。
式のmod7合同から整数合同を作り、既存の具体的Kummer単元補題へ渡す。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

/-- 分岐剰余の核が主イデアルで、lambdaは素元である。 -/
theorem uniformizer_prime : Prime ramifiedUniformizer := by
  apply (Ideal.span_singleton_prime ramifiedUniformizer_ne_zero).mp
  rw [← ramifiedPrime_eq_span_uniformizer]
  exact ramifiedPrime_isMaximal.isPrime

/-- 六次環の任意の七乗はmod7で整数に合同。実性や単元性は要求しない。 -/
theorem seventh_congr_integer (x : CC) :
    ∃ n : ℤ, (7 : CC) ∣ x ^ 7 - (n : CC) := by
  let n : ℤ := (ramifiedEval x).val
  have hn : ramifiedUniformizer ∣ x - (n : CC) := by
    apply (ramifiedEval_eq_zero_iff_dvd _).mp
    simp only [map_sub, n, Int.cast_natCast, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := hn
  have hx : x = ramifiedUniformizer * w + (n : CC) := by linear_combination hw
  refine ⟨n ^ 7, ?_⟩
  rw [Int.cast_pow, hx]
  apply Nat.Prime.dvd_add_pow_sub_pow_of_dvd (ramifiedUniformizer * w) (n : CC)
    (by decide : Nat.Prime 7)
  · rw [mul_pow]
    exact dvd_mul_of_dvd_left
      (seven_dvd_uniformizer_six.trans (pow_dvd_pow ramifiedUniformizer (by decide : 6 ≤ 7))) _
  · exact dvd_mul_right _ _

/-- 非分岐なXは7とも互いに素。7=lambda^6*unitを使う。 -/
theorem coprime_seven_of_away {x : CC} (hx : ¬ ramifiedUniformizer ∣ x) :
    IsCoprime (7 : CC) x := by
  have h := (uniformizer_prime.irreducible.coprime_iff_not_dvd).mpr hx
  have hp : IsCoprime (ramifiedUniformizer ^ 6) x := h.pow_left
  exact hp.of_isCoprime_of_dvd_left seven_dvd_uniformizer_six

/-- 二項式のmod7消滅から、係数比がある七乗に合同になる。 -/
theorem ratio_congr_seventh {x y : CC} (u v : CCˣ)
    (hx : ¬ ramifiedUniformizer ∣ x)
    (h : (7 : CC) ∣ (u : CC) * x ^ 7 + (v : CC) * y ^ 7) :
    ∃ a : CC, (7 : CC) ∣ ((u / v : CCˣ) : CC) - a ^ 7 := by
  obtain ⟨a, b, hab⟩ := coprime_seven_of_away hx
  have hbx : (7 : CC) ∣ b * x - 1 := by
    refine ⟨-a, ?_⟩
    linear_combination hab
  have hbpow := hbx.trans (sub_one_dvd_pow_sub_one (b * x) 7)
  have hs : (7 : CC) ∣ ((u / v : CCˣ) : CC) * (b * x) ^ 7 + (b * y) ^ 7 := by
    convert dvd_mul_of_dvd_right h ((↑v⁻¹ : CC) * b ^ 7) using 1
    simp only [div_eq_mul_inv, Units.val_mul]
    have hv : (↑v⁻¹ : CC) * (v : CC) = 1 := v.inv_val
    linear_combination -(b * y) ^ 7 * hv
  refine ⟨-(b * y), ?_⟩
  convert dvd_sub hs (dvd_mul_of_dvd_right hbpow (((u / v : CCˣ) : CC))) using 1
  ring

/-- 新しい係数比に整数合同を与え、既存Kummer単元補題を実際に適用する。 -/
theorem ratio_seventh {x y : CC} (u v : CCˣ)
    (hx : ¬ ramifiedUniformizer ∣ x)
    (h : (7 : CC) ∣ (u : CC) * x ^ 7 + (v : CC) * y ^ 7) :
    ∃ k : CCˣ, u / v = k ^ 7 := by
  obtain ⟨a, ha⟩ := ratio_congr_seventh u v hx h
  obtain ⟨n, hn⟩ := seventh_congr_integer a
  apply concrete_kummer_unit_power_criterion
  refine ⟨n, ?_⟩
  simpa only [Nat.cast_ofNat, sub_add_sub_cancel] using dvd_add ha hn

end
end DkMath.FLT.Kummer.SevenDescent
