/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerSelmer

#print "file: DkMathTest.FLT.FreyCyclotomicKummerSelmer"

namespace DkMathTest.FLT.FreyCyclotomicKummerSelmer

open DkMath.Lib.NumberTheory CyclicKummer KummerLocalValuation
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

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
    exact (FractionalIdeal.coeIdeal_span_singleton (2 : ℤ)).symm
  rw [he]
  exact FractionalIdeal.count_self ℚ twoPlace

private theorem selfMap : algebraMap ℤ ℤ = RingHom.id ℤ := RingHom.ext_int _ _

local instance : twoPlace.asIdeal.LiesOver twoPlace.asIdeal := ⟨by
    change twoPlace.asIdeal = Ideal.comap (algebraMap ℤ ℤ) twoPlace.asIdeal
    rw [selfMap, Ideal.comap_id]⟩

private theorem self_ramification : twoPlace.asIdeal.ramificationIdx' twoPlace.asIdeal = 1 := by
  have h := Ideal.ramificationIdx'_map_self_eq_one (R := ℤ) (S := ℤ) (p := twoPlace.asIdeal)
    (by simpa only [selfMap, Ideal.map_id] using twoPlace.isPrime.ne_top)
    (by simpa only [selfMap, Ideal.map_id] using twoPlace.ne_bot)
  simpa only [selfMap, Ideal.map_id] using h

-- The actual constant 2 cannot be a rational square: its exponent at (2) is 1.
private theorem two_not_square (a : ℚ) : a ^ 2 ≠ 2 := by
  intro ha
  have hd := count_dvd_of_ramification_eq_one (F := ℚ) (M := ℚ)
    twoPlace twoPlace 2 a two ha self_ramification
  rw [count_two] at hd
  norm_num at hd

private abbrev quadPoly : ℚ[X] := X ^ 2 - C 2
private instance : Fact (Irreducible (X ^ 2 - C (2 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 2)).mpr two_not_square⟩
private abbrev M := AdjoinRoot quadPoly

private def presentation : Presentation 2 ℚ M where
  radical := AdjoinRoot.root quadPoly
  constant := 2
  radical_pow := root_X_pow_sub_C_pow 2 (2 : ℚ)
  adjoin_eq_top := IntermediateField.adjoin_root_eq_top quadPoly
  irreducible := Fact.out

-- A genuine square-root extension has an actual prime over (2) where e is not 1.
-- The existence of alpha^2=2 alone cannot give a Selmer condition or trivial inertia.
example : ∃ w : HeightOneSpectrum (𝓞 M),
    w.asIdeal.LiesOver twoPlace.asIdeal ∧ twoPlace.asIdeal.ramificationIdx' w.asIdeal ≠ 1 := by
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral twoPlace.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 M))]; exact bot_le)
  have : W.IsMaximal := hWmax
  have : W.LiesOver twoPlace.asIdeal := ⟨hWv.symm⟩
  let w : HeightOneSpectrum (𝓞 M) :=
    ⟨W, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot twoPlace.ne_bot W⟩
  refine ⟨w, inferInstance, ?_⟩
  intro he
  have hd := count_dvd_of_ramification_eq_one (F := ℚ) (M := M)
    twoPlace w 2 presentation.radical two presentation.radical_pow he
  rw [count_two] at hd
  norm_num at hd

private def fractionalConstant : ℚˣ := Units.mk0 (1 / 4) (by norm_num)

-- Fractional constants and negative principal-ideal exponents retain the sign and normalization.
example : FractionalIdeal.count ℚ twoPlace
    (FractionalIdeal.spanSingleton ℤ⁰ (fractionalConstant : ℚ)) = -2 ∧
    (2 : ℤ) ∣ FractionalIdeal.count ℚ twoPlace
      (FractionalIdeal.spanSingleton ℤ⁰ (fractionalConstant : ℚ)) := by
  have hb : (fractionalConstant : ℚ) = (two : ℚ)⁻¹ ^ 2 := by norm_num [fractionalConstant, two]
  constructor
  · rw [hb, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow,
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, count_two]
    norm_num
  · exact count_dvd_of_ramification_eq_one (F := ℚ) (M := ℚ) twoPlace twoPlace
      2 (1 / 2) fractionalConstant (by norm_num [fractionalConstant]) self_ramification

#print axioms log_pow_eq_ramification_mul
#print axioms count_dvd_of_ramification_eq_one
#print axioms ramification_eq_one_of_inertia_fixes_radical
#print axioms count_dvd_of_inertia_fixes_radical
#print axioms CyclotomicKummerSelmer.finite_inertia_fixes_radical
#print axioms CyclotomicKummerSelmer.constantVector_mem_valuationSpace_of_absolute_inertia
#print axioms DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace
#print axioms DkMath.FLT.Frey.Source.residual_kummer_mem_selmer
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_resonant_absorption

end
end DkMathTest.FLT.FreyCyclotomicKummerSelmer
