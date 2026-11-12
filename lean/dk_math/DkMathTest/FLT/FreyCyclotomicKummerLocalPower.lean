/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerLocalPower

#print "file: DkMathTest.FLT.FreyCyclotomicKummerLocalPower"

namespace DkMathTest.FLT.FreyCyclotomicKummerLocalPower

open DkMath.Lib.NumberTheory NumberFieldCompletionComparison KummerLocalPower
open IsDedekindDomain CyclicKummer
open scoped NumberField nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
noncomputable section

private def twoPlaceZ : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(2 : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))
  ne_bot := by simp only [ne_eq, Ideal.span_singleton_eq_bot]; decide

private def v : HeightOneSpectrum (𝓞 ℚ) :=
  HeightOneSpectrum.comap Rat.ringOfIntegersEquiv Rat.ringOfIntegersEquiv.surjective twoPlaceZ

private theorem v_span : v.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
  change Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(2 : ℤ)}) = _
  rw [← Ideal.map_symm Rat.ringOfIntegersEquiv, Ideal.map_span, Set.image_singleton]
  simp only [map_ofNat]

private def two : ℚˣ := Units.mk0 2 (by decide)

private theorem count_two : FractionalIdeal.count ℚ v
    (FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ (two : ℚ)) = 1 := by
  have he : FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ (two : ℚ) =
      (v.asIdeal : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [v_span]
    exact (FractionalIdeal.coeIdeal_span_singleton (2 : 𝓞 ℚ)).symm
  rw [he]
  exact FractionalIdeal.count_self ℚ v

local instance : Algebra (𝓞 ℚ) (𝓞 ℚ) := NumberField.inst_ringOfIntegersAlgebra ℚ ℚ

local instance : v.asIdeal.LiesOver v.asIdeal := ⟨by
  change v.asIdeal = Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) v.asIdeal
  rw [show algebraMap (𝓞 ℚ) (𝓞 ℚ) = RingHom.id _ from RingHom.ext fun a => Subtype.ext (by simp)]
  simp⟩

private def identityPresentation : Presentation 1 ℚ ℚ where
  radical := 1
  constant := 1
  radical_pow := by simp
  adjoin_eq_top := Subsingleton.elim _ _
  irreducible := by simpa only [pow_one] using (Polynomial.irreducible_X_sub_C (1 : ℚ))

private theorem selfEF : v.asIdeal.ramificationIdx' v.asIdeal = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
  apply KummerDecomposition.ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    identityPresentation v v
  intro σ _
  exact map_one σ

-- The canonical map agrees with identity on the entire completion, not just global elements.
example : completionMap v v = RingHom.id (v.adicCompletion ℚ) := by
  apply RingHom.ext
  intro x
  refine (HeightOneSpectrum.denseRange_algebraMap ℚ v).induction_on
    (p := fun y => completionMap v v y = y) x
    (isClosed_eq (completionMap_isUniformInducing_of_ramification_eq_one v v selfEF.1).uniformContinuous.continuous
      continuous_id) ?_
  intro a
  rw [completionMap_algebraMap]
  rfl

example : letI A := completionAlgebra v v
    letI := A.toModule
    Module.finrank (v.adicCompletion ℚ) (v.adicCompletion ℚ) = 1 :=
  finrank_completion_eq_one_of_ef_eq_one v v selfEF.1 selfEF.2

-- A locally integral fraction has an actual global integer matching its first residue digit.
example : ∃ a : 𝓞 ℚ, v.valuation ℚ ((1 / 3 : ℚ) - algebraMap (𝓞 ℚ) ℚ a) < 1 := by
  have h3 : (3 : 𝓞 ℚ) ∈ v.asIdeal.primeCompl := by
    change Rat.ringOfIntegersEquiv (3 : 𝓞 ℚ) ∉ Ideal.span {(2 : ℤ)}
    rw [show Rat.ringOfIntegersEquiv (3 : 𝓞 ℚ) = (3 : ℤ) from map_ofNat _ _]
    norm_num [Ideal.mem_span_singleton]
  have hv3 : v.valuation ℚ (3 : ℚ) = 1 := by
    have h := (v.intValuation_eq_one_iff_mem_primeCompl _).mpr h3
    simpa only [← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ), map_ofNat] using h
  apply exists_integer_digit_of_inertiaDeg_eq_one v v selfEF.2 (1 / 3)
  rw [map_div₀, map_one, hv3, div_one]

-- There is no square root of 2 in the actual 2-adic completion: the valuation exponent is odd.
example : ¬ ∃ t : v.adicCompletion ℚ, t ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (2 : ℚ) := by
  rintro ⟨t, ht⟩
  have hc := DedekindFractionalValuation.count_spanSingleton v (two : ℚ) two.ne_zero
  rw [count_two] at hc
  have hlog : WithZero.log (v.valuation ℚ (2 : ℚ)) = -1 := by
    change (1 : ℤ) = -WithZero.log (v.valuation ℚ (2 : ℚ)) at hc
    omega
  have hh := congrArg (fun x : v.adicCompletion ℚ => WithZero.log (Valued.v x)) ht
  rw [map_pow, WithZero.log_pow] at hh
  have hv : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (2 : ℚ)) = v.valuation ℚ (2 : ℚ) := by
    exact v.valuedAdicCompletion_eq_valuation' (2 : ℚ)
  rw [hv, hlog] at hh
  simp only [nsmul_eq_mul] at hh
  omega

-- Track the same epsilon=9 through b=1/4=9*(1/6)^2 and the same local root t=1/2.
example : ∃ s : (v.adicCompletion ℚ)ˣ,
    s = Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom (Units.mk0 3 (by norm_num)) ∧
    (s : v.adicCompletion ℚ) ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (9 : ℚ) := by
  let φ := algebraMap ℚ (v.adicCompletion ℚ)
  let c : ℚˣ := Units.mk0 (1 / 6) (by norm_num)
  let t : (v.adicCompletion ℚ)ˣ := Units.map φ.toMonoidHom (Units.mk0 (1 / 2) (by norm_num))
  have hdecomp : (1 / 4 : ℚ) = 9 * (c : ℚ) ^ 2 := by norm_num [c]
  have ht : (t : v.adicCompletion ℚ) ^ 2 = φ (1 / 4) := by
    change (φ (1 / 2)) ^ 2 = φ (1 / 4)
    rw [← map_pow]
    norm_num
  refine ⟨t / Units.map φ.toMonoidHom c, ?_, unit_pow_of_constant_pow φ c t hdecomp ht⟩
  apply Units.ext
  rw [Units.val_div_eq_div_val]
  change φ (1 / 2) / φ (1 / 6) = φ 3
  rw [← map_div₀]
  norm_num

#print axioms exists_integer_digit_of_inertiaDeg_eq_one
#print axioms exists_approximation_of_ef_eq_one
#print axioms exists_valuation_sub_lt_of_ef_eq_one
#print axioms completionMap_algebraMap
#print axioms completionMap_isUniformInducing_of_ramification_eq_one
#print axioms denseRange_valuedMap_of_ef_eq_one
#print axioms completionMap_denseRange_of_ef_eq_one
#print axioms completionMap_bijective_of_ef_eq_one
#print axioms finrank_completion_eq_one_of_ef_eq_one
#print axioms exists_unit_pow_constant_of_ef_eq_one
#print axioms unit_pow_of_constant_pow
#print axioms DkMath.FLT.Frey.Source.residual_kummer_local_radical_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_constant_is_local_power_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_is_local_power_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_and_local_power

end
end DkMathTest.FLT.FreyCyclotomicKummerLocalPower
