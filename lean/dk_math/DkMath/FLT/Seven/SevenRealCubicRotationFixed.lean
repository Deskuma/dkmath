/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicThetaCoordinates

#print "file: DkMath.FLT.Seven.SevenRealCubicRotationFixed"

/-!
# 実三次環における mod 7 の回転固定性

既存の整数三座標と theta 座標を用い、回転固定剰余が整数の像であることを証明する。
実三次環専用の補題として保持し、Lib への一般化は行わない。
-/

namespace DkMath.FLT.Seven.SevenRealCubicInt

/-! ## mod 7 で回転固定な元は整数に合同する -/

/-- 整数基底の各座標で7可除性を検査する。剰余体の評価で零になる条件より強い。
`R/(alpha-3)` と `R/7R` を区別するため、三座標すべてを保持する。 -/
theorem seven_dvd_iff_coordinates (x : SevenRealCubicInt) :
    (7 : SevenRealCubicInt) ∣ x ↔
      (7 : ℤ) ∣ x.fst ∧ (7 : ℤ) ∣ x.snd ∧ (7 : ℤ) ∣ x.thd := by
  have hseven : (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ := rfl
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨w.fst, by simpa [hseven] using congrArg fst hw⟩,
      ⟨w.snd, by simpa [hseven] using congrArg snd hw⟩,
      ⟨w.thd, by simpa [hseven] using congrArg thd hw⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    exact ⟨⟨a, b, c⟩, by ext <;> simp_all⟩

/-- theta=alpha−3 に対する回転差の一次座標は 3B。有限の座標計算である。 -/
theorem rotation_gap_thetaLinear_mod_seven (x : SevenRealCubicInt) :
    thetaLinearModSeven (rotateEquiv x - x) = 3 * thetaLinearModSeven x := by
  simp only [thetaLinearModSeven, snd_sub, thd_sub, rotateEquiv_apply,
    rotateHom_snd, rotateHom_thd, Int.cast_sub, Int.cast_add, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat]
  have hseven : (7 : ZMod 7) = 0 := rfl
  linear_combination -3 * (x.thd : ZMod 7) * hseven

/-- 回転差の二次座標は B+C。従って回転固定なら B=C=0 となる。 -/
theorem rotation_gap_thetaSquare_mod_seven (x : SevenRealCubicInt) :
    thetaSquareModSeven (rotateEquiv x - x) = thetaLinearModSeven x + thetaSquareModSeven x := by
  simp only [thetaSquareModSeven, thetaLinearModSeven, thd_sub, rotateEquiv_apply,
    rotateHom_thd, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  have hseven : (7 : ZMod 7) = 0 := rfl
  linear_combination -(x.thd : ZMod 7) * hseven

/-- mod 7 で回転固定なら、整数基底の定数座標 x.fst に合同する。
回転差の三次座標が x.snd、定数座標が 2*x.thd であることを使う。
存在だけでなく、合同先の整数を明示している。 -/
theorem rotation_fixed_mod_seven_fst (x : SevenRealCubicInt)
    (h : (7 : SevenRealCubicInt) ∣ rotateEquiv x - x) :
    (7 : SevenRealCubicInt) ∣ x - (x.fst : SevenRealCubicInt) := by
  obtain ⟨w, hw⟩ := h
  have hseven : (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ := rfl
  have hb : x.snd = 7 * w.thd := by simpa [hseven] using congrArg thd hw
  have hc : 2 * x.thd = 7 * w.fst := by simpa [hseven] using congrArg fst hw
  rw [seven_dvd_iff_coordinates]
  refine ⟨by simp, ?_, ?_⟩
  · simpa using (show (7 : ℤ) ∣ x.snd from ⟨w.thd, hb⟩)
  · have hd : (7 : ℤ) ∣ x.thd := by
      refine ⟨x.thd - 3 * w.fst, ?_⟩
      linear_combination -3 * hc
    simpa using hd

/-- mod 7 の Galois 回転固定性から整数合同を回復する。
有理数の整数性や平均化を仮定せず、実三次環の整数三座標で証明する。 -/
theorem rotation_fixed_mod_seven_integer (x : SevenRealCubicInt)
    (h : (7 : SevenRealCubicInt) ∣ rotateEquiv x - x) :
    ∃ n : ℤ, (7 : SevenRealCubicInt) ∣ x - (n : SevenRealCubicInt) :=
  ⟨x.fst, rotation_fixed_mod_seven_fst x h⟩

/-- 整数合同は回転固定性に必要十分。整数自体に等しいという結論ではない。 -/
theorem rotation_fixed_mod_seven_iff_integer (x : SevenRealCubicInt) :
    (7 : SevenRealCubicInt) ∣ rotateEquiv x - x ↔
      ∃ n : ℤ, (7 : SevenRealCubicInt) ∣ x - (n : SevenRealCubicInt) := by
  refine ⟨rotation_fixed_mod_seven_integer x, ?_⟩
  rintro ⟨n, w, hw⟩
  have he : x = (n : SevenRealCubicInt) + 7 * w := by linear_combination hw
  refine ⟨rotateEquiv w - w, ?_⟩
  rw [he, map_add, map_mul, map_intCast, map_ofNat]
  ring

end DkMath.FLT.Seven.SevenRealCubicInt
