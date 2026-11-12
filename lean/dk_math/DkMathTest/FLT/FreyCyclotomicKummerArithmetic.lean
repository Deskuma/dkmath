/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerArithmetic

namespace DkMathTest.FLT.FreyCyclotomicKummerArithmetic

open DkMath.Lib.NumberTheory CyclicKummer CyclicKummerIntegral CyclotomicKummerWeight
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors
noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def quadPoly : ℚ[X] := X ^ 2 - C (-1)

private theorem quad_irreducible : Irreducible quadPoly := by
  apply (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 2)).mpr
  intro z
  nlinarith [sq_nonneg z]

private instance : Fact (Irreducible quadPoly) := ⟨quad_irreducible⟩

private def quadPresentation : Presentation 2 ℚ (AdjoinRoot quadPoly) where
  radical := AdjoinRoot.root quadPoly
  constant := -1
  radical_pow := root_X_pow_sub_C_pow 2 (-1)
  adjoin_eq_top := IntermediateField.adjoin_root_eq_top quadPoly
  irreducible := quad_irreducible

-- In an actual quadratic number field, start with the fractional radical i/2 and constant -1/4.
private def fractionalPresentation : Presentation 2 ℚ (AdjoinRoot quadPoly) :=
  rescale quadPresentation (1 / 2) (by norm_num)

example : fractionalPresentation.constant = -1 / 4 := by
  change (1 / 2 : ℚ) ^ 2 * (-1) = -1 / 4
  decide +kernel

-- Integerization constructs actual elements of BOTH integer rings and preserves the same equation.
example : ∃ D : IntegralModel fractionalPresentation,
    D.constant ≠ 0 ∧ D.radical ≠ 0 ∧
      (D.radical : AdjoinRoot quadPoly) ^ 2 = algebraMap ℚ _ (D.constant : ℚ) := by
  obtain ⟨D⟩ := exists_integral_model fractionalPresentation
  exact ⟨D, D.constant_ne_zero, D.radical_ne_zero, D.radical_pow⟩

-- Clearing a denominator by its fifth power keeps the original class correction explicit.
example : (2 : ℚ) ^ 5 * (1 / 2) = 16 := by decide +kernel

private def twoPlace : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(2 : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))
  ne_bot := by simp only [ne_eq, Ideal.span_singleton_eq_bot]; decide

private def two : ℚˣ := Units.mk0 2 (by decide)

private theorem count_two : FractionalIdeal.count ℚ twoPlace
    (FractionalIdeal.spanSingleton ℤ⁰ (two : ℚ)) = 1 := by
  have he : FractionalIdeal.spanSingleton ℤ⁰ (two : ℚ) =
      (twoPlace.asIdeal : FractionalIdeal ℤ⁰ ℚ) := by
    change FractionalIdeal.spanSingleton ℤ⁰ (algebraMap ℤ ℚ 2) =
      ((Ideal.span {(2 : ℤ)}) : FractionalIdeal ℤ⁰ ℚ)
    exact (FractionalIdeal.coeIdeal_span_singleton 2).symm
  rw [he]
  exact FractionalIdeal.count_self ℚ twoPlace

-- An integral constant need not satisfy the Selmer condition: ord_2(2)=1 is not divisible by 5.
private theorem two_not_selmer :
    Additive.ofMul (two : KummerClass ℚ 5) ∉ KummerSelmer.valuationSpace (R := ℤ) 5 := by
  intro h
  have hd := (KummerSelmer.mem_valuationSpace_mk_iff (R := ℤ) 5 two).mp h twoPlace
  rw [count_two] at hd
  exact (by decide : ¬ (5 : ℤ) ∣ 1) hd

example : IsIntegral ℤ (two : ℚ) ∧
    Additive.ofMul (two : KummerClass ℚ 5) ∉ KummerSelmer.valuationSpace (R := ℤ) 5 := by
  exact ⟨isIntegral_algebraMap, two_not_selmer⟩

-- The inverse fractional representative is nontrivial too; multiplying once by its denominator
-- would change it to 1. Integerization must use a pth-power correction.
example : ((two⁻¹ : ℚˣ) : KummerClass ℚ 5) ≠ 1 := by
  intro h
  have he : (two : KummerClass ℚ 5) = 1 := by
    have hi := congrArg (fun x : KummerClass ℚ 5 => x⁻¹) h
    simpa only [QuotientGroup.mk_inv, inv_inv, inv_one] using hi
  apply two_not_selmer
  rw [he]
  exact Submodule.zero_mem _

-- A genuine fifth power has valuation 5 at 2, so its class lies in the actual Selmer space.
example : Additive.ofMul ((two ^ 5 : ℚˣ) : KummerClass ℚ 5) ∈
    KummerSelmer.valuationSpace (R := ℤ) 5 := by
  have hp : ((two ^ 5 : ℚˣ) : KummerClass ℚ 5) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨two, rfl⟩
  rw [hp]
  exact Submodule.zero_mem _

-- The integer-ring unit injection supplies the all-prime condition for the actual unit -1.
example : Additive.ofMul
    (((Units.map (algebraMap ℤ ℚ).toMonoidHom (-1 : ℤˣ)) : ℚˣ) : KummerClass ℚ 5) ∈
      KummerSelmer.valuationSpace (R := ℤ) 5 := KummerSelmer.unit_mem_valuationSpace 5 (-1)

#print axioms CyclicKummerIntegral.rescale
#print axioms CyclicKummerIntegral.exists_integral_multiple
#print axioms CyclicKummerIntegral.exists_integral_power_multiple
#print axioms CyclicKummerIntegral.exists_integral_rescale
#print axioms CyclicKummerIntegral.exists_integral_model
#print axioms IntegralModel.radical_pow
#print axioms CyclotomicKummerArithmetic.rescale_constantClass
#print axioms CyclotomicKummerArithmetic.exists_integral_model_same_vector
#print axioms CyclotomicKummerArithmetic.rescale_mem_valuationSpace_iff
#print axioms CyclotomicKummerArithmetic.constantVector_mem_valuationSpace_iff
#print axioms KummerSelmer.mem_valuationSpace_iff_selmer
#print axioms KummerSelmer.count_span_eq_neg_valuation
#print axioms KummerSelmer.valuationLinear_eq_zero_iff
#print axioms KummerSelmer.unit_mem_valuationSpace
#print axioms KummerSelmer.count_span_mul_pow
#print axioms KummerSelmer.exists_fractionalIdeal_pow
#print axioms KummerSelmer.fractionalIdeal_pow_injective
#print axioms KummerSelmer.exists_classGroup_torsion
#print axioms DkMath.FLT.Frey.Source.residual_nonsplit_has_integral_weight_two_kummer_model

end
end DkMathTest.FLT.FreyCyclotomicKummerArithmetic
