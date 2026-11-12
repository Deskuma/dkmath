/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Frey

#print "file: DkMathTest.FLT.FreyArithmetic"

/-!
# NOTE-005 回帰例

p=1 の非零原始解 3+16=19 は source を実際に構成できる算術サンプル。
p≥4 の反例の存在を仮定した例とは区別する。素数2の補正・特異な零 Gap・
分母条件の不成立例により、都合のよい入力だけに合わせた恒等式を避ける。
37次の例は巨大な二項展開をせず、一般定理の特殊化として検査する。
-/

namespace FreyArithmeticTest

open DkMath.Lib.NumberTheory FreyGapCubic GNFreyDiscriminant FreyPrimeValuation
open DkMath.FLT.Frey

-- 実際の整数モデル [1,3,0,-3,0] と、その二つの不変量。
example : (integral 3 16).Δ = 3249 := by norm_num [integral, WeierstrassCurve.Δ,
  WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
example : (integral 3 16).c₄ = 313 := by
  norm_num [integral, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

-- 素朴な判別式と正規化後の判別式の倍率は4096。
example (A B : ℚ) : (naive A B).Δ = 4096 * (normalized A B).Δ := by
  rw [naive_discriminant, normalized_discriminant]
  ring

-- 整数除算を無条件で有理数除算へ置き換えられない例。
example : ¬ IntegralNormalization 1 1 := by
  intro h
  have hf := h.four
  norm_num at hf

-- a+b=0 の GN 恒等式は成立するが、その曲線は特異。
example : (normalized (1 : ℚ) (-1)).Δ = 0 := by
  norm_num [normalized_discriminant]
example : (1 : ℤ) ^ 37 + (-1) ^ 37 =
    (1 + -1) * gnFactor 37 (1 : ℤ) (-1) := sum_eq_gap_gn (by decide) _ _

-- 実際に source を構成する。p=1 の例から p≥4 の反例の存在を推論しない。
def sample : Source 1 where
  a := 3
  b := 16
  c := 19
  a_ne := by decide
  b_ne := by decide
  c_ne := by decide
  coprime := ⟨-5, 1, by norm_num⟩
  equation := by norm_num
  normalization := ⟨by norm_num, by norm_num⟩

example : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
example : sample.curve.map (Int.castRingHom ℚ) = sample.rationalCurve := sample.curve_map

section OddPrime
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- 奇素数3の付値は2。c₄は3で割れず、正規化してもこの局所情報が保持される。
example : padicValInt 3 sample.curve.Δ = 2 ∧ ¬ (3 : ℤ) ∣ sample.curve.c₄ := by
  have h := sample.local_arithmetic (by decide) (ℓ := 3) (by decide) (by norm_num [sample])
  constructor
  · have hv : padicValInt 3 (sample.a * sample.b * sample.c) = 1 := by
      change padicValNat 3 912 = 1
      rw [Nat.padicValNat_def]
      exact multiplicity_eq_of_dvd_of_not_dvd (by decide : 3 ^ 1 ∣ 912)
        (by decide : ¬ 3 ^ (1 + 1) ∣ 912)
    simpa only [hv, Nat.mul_one] using h.2.2.1
  · exact h.2.1

-- 5を法として実際に基底変換した曲線は非特異。
example : (sample.curve.map (Int.castRingHom (ZMod 5))).IsElliptic := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact sample.reduction_isElliptic (by decide) (by decide) (by norm_num [sample])

-- 37次 GN の付値表示。反例の方程式や類群の正則性を要求しない。
example (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hs : a ^ 37 + b ^ 37 ≠ 0) :
    padicValRat 3 (normalized (a ^ 37) (b ^ 37)).Δ =
      74 * (padicValRat 3 a + padicValRat 3 b) +
        2 * (padicValRat 3 (a + b) + padicValRat 3 (gnFactor 37 a b)) := by
  exact valuation_gn (by decide) (by decide) a b ha hb hs
end OddPrime

section Two
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
-- 2での補正は実際に消せない。Δ_norm の付値は 2·4−8=0。
example : padicValRat 2 (normalized (3 : ℚ) 16).Δ = 0 := by
  have h := valuation_of_solution (ℓ := 2) sample.equation sample.product_ne_zero
  have hv : padicValInt 2 (sample.a * sample.b * sample.c) = 4 := by
    change padicValNat 2 912 = 4
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide : 2 ^ 4 ∣ 912)
      (by decide : ¬ 2 ^ (4 + 1) ∣ 912)
  rw [hv, show padicValNat 2 2 = 1 from padicValNat.self (by decide)] at h
  norm_num [sample] at h
  exact h
example : padicValRat 2 ((3 * 16 * 19 : ℤ) : ℚ) = 4 := by
  rw [padicValRat.of_int]
  change (padicValNat 2 912 : ℤ) = 4
  have hv : padicValNat 2 912 = 4 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide : 2 ^ 4 ∣ 912)
      (by decide : ¬ 2 ^ (4 + 1) ∣ 912)
  rw [hv]
  norm_num
end Two

-- 37次の整係数性を、向き付け条件から供給する。3^37,2^37 は展開しない。
example : IntegralNormalization ((3 : ℤ) ^ 37) ((2 : ℤ) ^ 37) :=
  normalization_of_oriented (by decide) (by decide) (by norm_num) (by decide)

-- 原始性を落とすと c₄ の非可除性は壊れる。
example : (3 : ℤ) ∣ 3 * 3 * (3 + 3) ∧ (3 : ℤ) ∣ 3 ^ 2 + 3 * 3 + 3 ^ 2 := by
  norm_num

end FreyArithmeticTest
