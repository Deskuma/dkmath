/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerDecomposition

#print "file: DkMathTest.FLT.FreyCyclotomicKummerDecomposition"

namespace DkMathTest.FLT.FreyCyclotomicKummerDecomposition
open DkMath.Lib.NumberTheory CyclicKummer KummerLocalValuation KummerDecomposition
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors NumberField Pointwise
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

private instance : Algebra.IsQuadraticExtension ℚ M := ⟨by
  change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {quadPoly}) = 2
  rw [finrank_quotient_span_eq_natDegree]
  norm_num [quadPoly]⟩

private def twoPlaceQ : HeightOneSpectrum (𝓞 ℚ) :=
  HeightOneSpectrum.comap Rat.ringOfIntegersEquiv Rat.ringOfIntegersEquiv.surjective twoPlace

private theorem twoPlaceQ_span : twoPlaceQ.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
  change Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(2 : ℤ)}) = _
  rw [← Ideal.map_symm Rat.ringOfIntegersEquiv, Ideal.map_span, Set.image_singleton]
  simp only [map_ofNat]

private theorem count_two_Q : FractionalIdeal.count ℚ twoPlaceQ
    (FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ (two : ℚ)) = 1 := by
  have he : FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ (two : ℚ) =
      (twoPlaceQ.asIdeal : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [twoPlaceQ_span]
    exact (FractionalIdeal.coeIdeal_span_singleton (2 : 𝓞 ℚ)).symm
  rw [he]
  exact FractionalIdeal.count_self ℚ twoPlaceQ

local instance : twoPlaceQ.asIdeal.LiesOver twoPlaceQ.asIdeal := ⟨by
  change twoPlaceQ.asIdeal = Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) twoPlaceQ.asIdeal
  simp⟩

-- The same root equation alpha^2=2 does not force the decomposition group to be trivial.
-- Use a genuine prime above (2), and rule out both D=1 and e=1 by its ideal exponent.
example : ∃ w : HeightOneSpectrum (𝓞 M),
    w.asIdeal.LiesOver twoPlaceQ.asIdeal ∧
      MulAction.stabilizer (M ≃ₐ[ℚ] M) w.asIdeal ≠ ⊥ ∧
      twoPlaceQ.asIdeal.ramificationIdx' w.asIdeal ≠ 1 := by
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral twoPlaceQ.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 M))]; exact bot_le)
  have : W.IsMaximal := hWmax
  have : W.LiesOver twoPlaceQ.asIdeal := ⟨hWv.symm⟩
  let w : HeightOneSpectrum (𝓞 M) :=
    ⟨W, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot twoPlaceQ.ne_bot W⟩
  refine ⟨w, inferInstance, ?_, ?_⟩
  · intro hD
    have hfix : ∀ σ : M ≃ₐ[ℚ] M,
        σ ∈ MulAction.stabilizer (M ≃ₐ[ℚ] M) w.asIdeal → σ presentation.radical = presentation.radical := by
      intro σ hσ
      have he : σ = 1 := Subgroup.mem_bot.mp (hD ▸ hσ)
      rw [he]
      rfl
    have he := (ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
      presentation twoPlaceQ w hfix).1
    have hd := count_dvd_of_ramification_eq_one (F := ℚ) (M := M)
      twoPlaceQ w 2 presentation.radical two presentation.radical_pow he
    rw [count_two_Q] at hd
    norm_num at hd
  · intro he
    have hd := count_dvd_of_ramification_eq_one (F := ℚ) (M := M)
      twoPlaceQ w 2 presentation.radical two presentation.radical_pow he
    rw [count_two_Q] at hd
    norm_num at hd


private def identityPresentation : Presentation 1 ℚ ℚ where
  radical := 1
  constant := 1
  radical_pow := by simp
  adjoin_eq_top := Subsingleton.elim _ _
  irreducible := by simpa only [pow_one] using (irreducible_X_sub_C (1 : ℚ))

-- Positive test at the actual self-prime: both invariants, including the residue degree, are one.
example : twoPlaceQ.asIdeal.ramificationIdx' twoPlaceQ.asIdeal = 1 ∧
    twoPlaceQ.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
  apply ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    identityPresentation twoPlaceQ twoPlaceQ
  intro σ _
  exact map_one σ

#print axioms AbsoluteDecompositionLift.exists_lift_mem_integral_decomposition
#print axioms AbsoluteDecompositionLift.exists_valuation_decomposition_of_integral_stabilizer
#print axioms AbsoluteDecompositionLift.exists_lift_mem_valuation_decomposition
#print axioms subgroup_eq_bot_of_fixes_radical
#print axioms ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
#print axioms CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p
#print axioms CyclotomicKummerDecomposition.finite_decomposition_eq_bot_at_p
#print axioms CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_finite_decomposition_fixes_radical_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_decomposition_eq_bot_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_ramification_and_inertiaDeg_eq_one_at_p

end
end DkMathTest.FLT.FreyCyclotomicKummerDecomposition
