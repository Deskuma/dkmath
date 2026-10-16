/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicUnitClass
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier

/-!
# FLT7 教科書第一段：一次単元の相対ノルム

六次環を実三次環上の二次拡大として読む。整数合同をノルムへ移し、
既存の二成分射影対数から七乗根を取り出す。これは六次単元そのものの
七乗性ではない。共役との積を保持し、次段の位相解析の入力にする。
-/

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 実三次環の整数合同は二成分の射影対数を零にする。 -/
theorem realCubic_primary_unit_log_zero (u : SevenRealCubicIntˣ) (n : ℤ)
    (h : (7 : SevenRealCubicInt) ∣ (u : SevenRealCubicInt) - (n : SevenRealCubicInt)) :
    projectiveLog (Additive.ofMul u) = 0 := by
  obtain ⟨w, hw⟩ := h
  have hs : (7 : ℤ) ∣ (u : SevenRealCubicInt).snd := by
    refine ⟨w.snd, ?_⟩
    have hs := congrArg SevenRealCubicInt.snd hw
    simpa [show (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ from rfl] using hs
  have ht : (7 : ℤ) ∣ (u : SevenRealCubicInt).thd := by
    refine ⟨w.thd, ?_⟩
    have ht := congrArg SevenRealCubicInt.thd hw
    simpa [show (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ from rfl] using ht
  have hs0 : ((u : SevenRealCubicInt).snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hs
  have ht0 : ((u : SevenRealCubicInt).thd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr ht
  rw [projectiveLog_apply]
  ext <;> simp [unitNilpotentX, unitNilpotentY, thetaLinearModSeven,
    thetaSquareModSeven, hs0, ht0]

/-- 既存の七乗判定を実際に適用する。追加の類数・単元分類仮定を要求しない。 -/
theorem realCubic_primary_unit_seventh (u : SevenRealCubicIntˣ)
    (h : ∃ n : ℤ, (7 : SevenRealCubicInt) ∣ (u : SevenRealCubicInt) - (n : SevenRealCubicInt)) :
    ∃ v : SevenRealCubicIntˣ, u = v ^ 7 := by
  obtain ⟨n, hn⟩ := h
  exact (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero u).mpr
    (realCubic_primary_unit_log_zero u n hn)

/-- 六次環から実三次環への相対ノルム。二次代数の乗法的ノルムを使う。 -/
abbrev relativeNorm : SevenCyclotomicDegreeSixInt.Ring →* SevenRealCubicInt :=
  QuadraticAlgebra.norm

/-- `x = n + 7w` の二次ノルムを展開する。
整数は二次拡大で `n²` に写るため、ノルム側の合同先は `n` ではなく `n²`。 -/
theorem relativeNorm_congruent_integer
    {x : SevenCyclotomicDegreeSixInt.Ring} {n : ℤ}
    (h : (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ x - (n : _)) :
    (7 : SevenRealCubicInt) ∣ relativeNorm x - (n : SevenRealCubicInt) ^ 2 := by
  obtain ⟨w, hw⟩ := h
  have hx : x = (n : _) + 7 * w := by linear_combination hw
  refine ⟨(n : SevenRealCubicInt) * (2 * w.re + (alpha - 1) * w.im) +
    7 * relativeNorm w, ?_⟩
  rw [hx]
  simp only [relativeNorm, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  ring

/-- 六次の一次単元の相対ノルムは実三次単元の七乗。
ノルムは単射ではないので、この結論から元の単元の七乗性はまだ従わない。 -/
theorem relativeNorm_primary_unit_seventh
    (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (h : ∃ n : ℤ, (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ (u : _) - (n : _)) :
    ∃ v : SevenRealCubicIntˣ, Units.map relativeNorm u = v ^ 7 := by
  apply realCubic_primary_unit_seventh
  obtain ⟨n, hn⟩ := h
  refine ⟨n ^ 2, ?_⟩
  simpa only [Units.coe_map, Int.cast_pow] using relativeNorm_congruent_integer hn

/-- 位相情報を捨てない形のノルム根復元。
`u * star u = ofReal(v)^7` を得る。次章では共役比の解析と組み合わせる。 -/
theorem primary_unit_mul_conjugate
    (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (h : ∃ n : ℤ, (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ (u : _) - (n : _)) :
    ∃ v : SevenRealCubicIntˣ,
      (u : SevenCyclotomicDegreeSixInt.Ring) * star (u : SevenCyclotomicDegreeSixInt.Ring) =
        SevenCyclotomicDegreeSixInt.ofReal (v : SevenRealCubicInt) ^ 7 := by
  obtain ⟨v, hv⟩ := relativeNorm_primary_unit_seventh u h
  refine ⟨v, ?_⟩
  have hv' : relativeNorm (u : SevenCyclotomicDegreeSixInt.Ring) =
      (v : SevenRealCubicInt) ^ 7 := congrArg Units.val hv
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_pow, ← hv']
  rfl

end DkMath.FLT.Kummer.SevenPrimaryNorm
