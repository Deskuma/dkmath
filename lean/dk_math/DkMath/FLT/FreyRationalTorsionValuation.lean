/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Frey
import DkMath.Lib.NumberTheory.RationalTwoAdicBounds

#print "file: DkMath.FLT.FreyRationalTorsionValuation"

/-!
# NOTE-030-002: 同じSourceの係数を2進付値へ翻訳する

a₂の整性は`curve_map`で整数モデルの係数へ戻すだけで得られる。
従ってmod 4の向き付けを再証明せず、全Sourceについてこの整性を使える。
一方、a₄の付値をγ=p v₂(b)−4とするにはbの偶数性を明示的に要求する。
原始性からaの奇数性を取り出し、a,bの非零性を保持して積・冪・商を評価する。

この段階は係数の算術であり、有理点の付値の上下界や有理torsion排除ではない。
p≥5はγ≥1を得る箇所でだけ要求し、素数性やa≡3 mod4を暗黙に追加しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory FreyGapCubic RationalTwoAdicBounds
variable {p : ℕ} (S : Source p)

/-- 元の正規化モデルはa₁=1である。 -/
theorem rationalCurve_a₁ : S.rationalCurve.a₁ = 1 := rfl

/-- 元の正規化モデルはa₃=0である。 -/
theorem rationalCurve_a₃ : S.rationalCurve.a₃ = 0 := rfl

/-- 元の正規化モデルはa₆=0であり、(0,0)の構造に利用できる。 -/
theorem rationalCurve_a₆ : S.rationalCurve.a₆ = 0 := rfl

/-- a₄を元のa,bと分母16を保った式で公開する。 -/
theorem rationalCurve_a₄ :
    S.rationalCurve.a₄ = -((S.a : ℚ) ^ p * (S.b : ℚ) ^ p) / 16 := rfl

/-- 整数モデルの係数を写すだけでa₂の2進整性が得られる。
向き付けの偶奇条件も、指数の素数性も不要である。 -/
theorem a₂_twoAdic_integral : Lower 0 S.rationalCurve.a₂ := by
  have h := congrArg (fun E : WeierstrassCurve ℚ => E.a₂) S.curve_map
  change (S.curve.a₂ : ℚ) = S.rationalCurve.a₂ at h
  rw [← h]
  exact lower_int _

/-- 有理torsionの付値軌道で使う深さ。正値性を定義に組み込まず、別に証明する。 -/
def twoAdicGamma : ℤ := (p : ℤ) * (padicValInt 2 S.b : ℤ) - 4

/-- bが偶数なら、原始性によりaは2で割れない。分母条件からは推論しない。 -/
theorem not_two_dvd_a_of_b_even (hbe : Even S.b) : ¬ (2 : ℤ) ∣ S.a := by
  intro ha
  have hb : (2 : ℤ) ∣ S.b := even_iff_two_dvd.mp hbe
  obtain ⟨u, v, huv⟩ := S.coprime
  have hd : (2 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)
  norm_num at hd

/-- bの偶数性と原始性から得るaの奇数性。 -/
theorem a_odd_of_b_even (hbe : Even S.b) : Odd S.a :=
  Int.not_even_iff_odd.mp (fun h => S.not_two_dvd_a_of_b_even hbe (even_iff_two_dvd.mp h))

/-- aは非零の2進単元である。付値0だけでは非零性を代用しない。 -/
theorem a_twoAdic_unit (hbe : Even S.b) : Exact 0 (S.a : ℚ) := by
  refine ⟨by exact_mod_cast S.a_ne, ?_⟩
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (S.not_two_dvd_a_of_b_even hbe)]
  rfl

/-- 非零のbの正確な付値を、整数側の自然数値と照合する。 -/
theorem b_twoAdic_exact : Exact (padicValInt 2 S.b : ℤ) (S.b : ℚ) :=
  ⟨by exact_mod_cast S.b_ne, padicValRat.of_int⟩

/-- 非零の偶数bは2進付値1以上。零での付値の便宜値は使わない。 -/
theorem b_twoAdic_positive (hbe : Even S.b) : 1 ≤ padicValInt 2 S.b := by
  rcases (padicValInt_dvd_iff (p := 2) 1 S.b).mp
      (by obtain ⟨r, hr⟩ := hbe; exact ⟨r, by norm_num; omega⟩) with h | h
  · exact (S.b_ne h).elim
  · exact h

/-- a₄の正確な付値γ。非零性、符号、冪p、分母16の寄与−4を全て保持する。 -/
theorem a₄_twoAdic_exact (hbe : Even S.b) : Exact S.twoAdicGamma S.rationalCurve.a₄ := by
  rw [S.rationalCurve_a₄]
  have h := (((S.a_twoAdic_unit hbe).pow p).mul (S.b_twoAdic_exact.pow p)).neg.div exact_sixteen
  simpa only [mul_zero, zero_add, twoAdicGamma] using h

/-- p≥5と非零偶数bからγ≥1が従う。指数の素数性はこの不等式には不要。 -/
theorem one_le_twoAdicGamma (hp5 : 5 ≤ p) (hbe : Even S.b) : 1 ≤ S.twoAdicGamma := by
  have hb : (1 : ℤ) ≤ padicValInt 2 S.b := by exact_mod_cast S.b_twoAdic_positive hbe
  have hp : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  dsimp only [twoAdicGamma]
  nlinarith

/-- p≥5の偶数bについて、a₄は深さ1以上である。 -/
theorem a₄_twoAdic_positive (hp5 : 5 ≤ p) (hbe : Even S.b) : Lower 1 S.rationalCurve.a₄ :=
  (S.a₄_twoAdic_exact hbe).lower.mono (S.one_le_twoAdicGamma hp5 hbe)

end DkMath.FLT.Frey.Source
