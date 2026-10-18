/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyArithmetic

#print "file: DkMathTest.FLT.FreyLocalReduction"

/-!
# NOTE-006 §4 の局所還元回帰例

既存の実在する p=1 解 3+16=19 を使用する。3と19では乗法的還元、
5と313では良還元。313は c₄ 自体を割るので、良還元を c₄ 単元性で
代用していないことも検査する。37次の例は仮想 source の一般定理の特殊化。
-/

namespace FreyLocalReductionTest
open DkMath.Lib.NumberTheory FreyLocalReduction
open DkMath.FLT.Frey
open FreyArithmeticTest (sample)

section Three
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
example : WeierstrassCurve.HasMultiplicativeReduction (LocalRing 3) sample.rationalCurve :=
  sample.hasMultiplicativeReduction (by decide) (by decide) (by norm_num [sample])
example : WeierstrassCurve.IsMinimal (LocalRing 3) sample.rationalCurve :=
  sample.isMinimal_at_odd_prime (by decide) (by decide)
example : ¬ WeierstrassCurve.HasGoodReduction (LocalRing 3) sample.rationalCurve :=
  WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction (LocalRing 3)
    (sample.hasMultiplicativeReduction (ℓ := 3) (by decide) (by decide)
    (by norm_num [sample]))
end Three

section Nineteen
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
example : WeierstrassCurve.HasMultiplicativeReduction (LocalRing 19) sample.rationalCurve :=
  sample.hasMultiplicativeReduction (by decide) (by decide) (by norm_num [sample])
end Nineteen

section Good
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 313) := ⟨by norm_num⟩
example : WeierstrassCurve.HasGoodReduction (LocalRing 5) sample.rationalCurve :=
  sample.hasGoodReduction (by decide) (by decide) (by norm_num [sample])
example : (313 : ℤ) ∣ sample.curve.c₄ := by
  norm_num [Source.curve, sample, FreyGapCubic.integral, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
example : WeierstrassCurve.HasGoodReduction (LocalRing 313) sample.rationalCurve :=
  sample.hasGoodReduction (by decide) (by decide) (by norm_num [sample])
example : ¬ WeierstrassCurve.HasMultiplicativeReduction (LocalRing 5) sample.rationalCurve :=
  WeierstrassCurve.HasGoodReduction.not_hasMultiplicativeReduction (LocalRing 5)
    (sample.hasGoodReduction (ℓ := 5) (by decide) (by decide)
    (by norm_num [sample]))
end Good

-- ℓ=p=37 も局所還元の結論には含まれる。表現の不分岐性は結論に含めない。
section ThirtySeven
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
example (S : Source 37) (hd : (37 : ℤ) ∣ S.a * S.b * S.c) :
    WeierstrassCurve.HasMultiplicativeReduction (LocalRing 37) S.rationalCurve :=
  S.hasMultiplicativeReduction (by decide) (by decide) hd
example (S : Source 37) :
    WeierstrassCurve.IsMinimal (LocalRing 37) S.rationalCurve ∧
      padicValRat 37 S.rationalCurve.Δ = 74 * (padicValInt 37 (S.a * S.b * S.c) : ℤ) :=
  S.minimal_discriminant_valuation (by decide) (by decide)
example (S : Source 37) :
    WeierstrassCurve.IsMinimal (LocalRing 37) S.rationalCurve ∧
      (37 : ℤ) ∣ padicValRat 37 S.rationalCurve.Δ :=
  S.minimal_discriminant_exponent_dvd (by decide) (by decide)
end ThirtySeven

end FreyLocalReductionTest
