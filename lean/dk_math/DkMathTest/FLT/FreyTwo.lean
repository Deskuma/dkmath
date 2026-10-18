/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTwo
import DkMathTest.FLT.FreyArithmetic

#print "file: DkMathTest.FLT.FreyTwo"

/-!
# NOTE-007 素数2の回帰例

p=1 の実在する source は2で良還元を持つため、p≥5 の前提は省けない。
37次は同じ source 型での条件付き特殊化。2で −8 を落とせないことも検査する。
-/
namespace FreyTwoTest
open DkMath.FLT.Frey DkMath.Lib.NumberTheory FreyGapCubic FreyLocalReduction
open FreyArithmeticTest (sample)
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : WeierstrassCurve.IsMinimal (LocalRing 2) sample.rationalCurve := sample.isMinimal_at_two
example : WeierstrassCurve.HasGoodReduction (LocalRing 2) sample.rationalCurve := by
  rw [← sample.curve_map]
  apply hasGoodReduction_at_prime
  norm_num [Source.curve, sample, integral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
example : ¬ IntegralNormalization (1 : ℤ) 1 := by
  intro h
  have hf := h.four
  norm_num at hf

example (S : Source 37) : WeierstrassCurve.HasMultiplicativeReduction (LocalRing 2) S.rationalCurve :=
  S.hasMultiplicativeReduction_at_two (by decide)
example (S : Source 37) : padicValRat 2 S.rationalCurve.Δ =
    74 * (padicValInt 2 (S.a * S.b * S.c) : ℤ) - 8 :=
  S.minimal_discriminant_valuation_two.2
example (S : Source 37) : ¬ (37 : ℤ) ∣ padicValRat 2 S.rationalCurve.Δ := by
  intro hd
  have h8 := S.exponent_dvd_two_valuation_iff.mp hd
  norm_num at h8
example (S : Source 37) {ℓ : ℕ} [Fact ℓ.Prime] :
    WeierstrassCurve.HasMultiplicativeReduction (LocalRing ℓ) S.rationalCurve ↔
      (ℓ : ℤ) ∣ S.a * S.b * S.c := S.multiplicative_support_iff (by decide)
example (S : Source 37) {ℓ : ℕ} [Fact ℓ.Prime] :
    WeierstrassCurve.HasGoodReduction (LocalRing ℓ) S.rationalCurve ∨
      WeierstrassCurve.HasMultiplicativeReduction (LocalRing ℓ) S.rationalCurve :=
  S.good_or_multiplicative_every_prime (by decide)
end FreyTwoTest
