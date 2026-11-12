/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerWeight

namespace DkMathTest.FLT.FreyCyclotomicKummerWeight

open DkMath.Lib.NumberTheory CyclotomicKummerWeight DkMath.Lib.Algebra
noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- Equality of Kummer classes is weaker than equality of their representatives.
example : let u : ℚˣ := Units.mk0 2 (by decide)
    ((u ^ 5 : ℚˣ) : KummerClass ℚ 5) = 1 := by
  exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.mk0 2 (by decide), rfl⟩

example : (2 : ℚ) ^ 5 ≠ 1 := by decide +kernel

private def two : (ZMod 11)ˣ := Units.mk0 2 (by decide)

-- A nontrivial actual Kummer class in F_11^*/(F_11^*)^5.
example : (two : KummerClass (ZMod 11) 5) ≠ 1 := by
  intro h
  have hm : two ∈ powerSubgroup (ZMod 11)ˣ 5 := (QuotientGroup.eq_one_iff two).mp h
  exact (by decide +kernel : ¬ ∃ u : (ZMod 11)ˣ, u ^ 5 = two) hm

-- The square weight at 2 mod 5 is 4; the inverse weight would be 3.
example : ((2 : ZMod 5) ^ 2).val = 4 ∧ ((2 : ZMod 5)⁻¹).val = 3 := by decide +kernel

-- These two weights act differently on an actual nontrivial Kummer class.
example : (two : KummerClass (ZMod 11) 5) ^ 4 ≠ (two : KummerClass (ZMod 11) 5) ^ 3 := by
  intro h
  have he : ((two ^ 4 : (ZMod 11)ˣ) : KummerClass (ZMod 11) 5) =
      ((two ^ 3 : (ZMod 11)ˣ) : KummerClass (ZMod 11) 5) := by
    simpa only [QuotientGroup.mk_pow] using h
  have hm : two ^ 4 / two ^ 3 ∈ powerSubgroup (ZMod 11)ˣ 5 := QuotientGroup.eq_iff_div_mem.mp he
  exact (by decide +kernel : ¬ ∃ u : (ZMod 11)ˣ, u ^ 5 = two ^ 4 / two ^ 3) hm

-- A field containing no nontrivial fifth-power quotient must not manufacture a nonzero class.
example (u : (ZMod 7)ˣ) : (u : KummerClass (ZMod 7) 5) = 1 := by
  have hs : ∀ u : (ZMod 7)ˣ, ∃ v : (ZMod 7)ˣ, v ^ 5 = u := by decide +kernel
  exact (QuotientGroup.eq_one_iff _).mpr (hs u)

-- In particular the square weight of a sign is trivial, not its inverse sign.
example : ((-1 : ZMod 5) ^ 2).val = 1 := by decide +kernel

#print axioms KummerRadicalCharacter.radicalCharacter
#print axioms KummerRadicalCharacter.radicalCharacter_eq_one_iff
#print axioms KummerRadicalCharacter.factor_apply
#print axioms KummerRadicalCharacter.map_scalar
#print axioms KummerRadicalCharacter.conjugate_ratio
#print axioms CyclotomicKummerWeight.baseCharacter_lift
#print axioms CyclotomicKummerWeight.presentationCharacter_kernel
#print axioms CyclotomicKummerWeight.conjugate_ratio
#print axioms CyclotomicKummerWeight.conjugate_radical_div_mem
#print axioms CyclotomicKummerWeight.constant_weight_square
#print axioms CyclotomicKummerWeight.base_constant_weight_square
#print axioms CyclotomicKummerWeight.constantClass_ne_one
#print axioms CyclotomicKummerWeight.constantClass_weight_square
#print axioms CyclotomicKummerWeight.classLinearMap
#print axioms CyclotomicKummerWeight.constantVector_ne_zero
#print axioms CyclotomicKummerWeight.constantVector_weight_square
#print axioms DkMath.FLT.Frey.Source.residual_nonsplit_has_weight_two_kummer_class

end
end DkMathTest.FLT.FreyCyclotomicKummerWeight
