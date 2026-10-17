/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGNDescent

#print "file: DkMathTest.FLT.Kummer.FiveGNDescent"

open scoped NumberField
open DkMath.FLT.Kummer DkMath.FLT.Five DkMath.Lib.NumberTheory

-- A real primary unit of infinite order, without a hypothetical FLT solution.
example : ∃ y : GoldenInt, IsUnit y ∧ goldenPhi ^ 5 = y ^ 5 := by
  apply golden_unit_fifth_of_integer_congruence ((goldenUnit_iff_isUnit.mp goldenUnit_phi).pow 5)
  refine ⟨3, goldenPhi, ?_⟩
  decide +kernel

-- The modulus is necessary: φ is a unit but is not congruent to any integer mod 5.
example (n : ℤ) : ¬ (5 : GoldenInt) ∣ goldenPhi - (n : GoldenInt) := by
  rintro ⟨w, hw⟩
  have hs := congrArg GoldenInt.snd hw
  change (goldenSub goldenPhi (goldenOfInt n)).snd = (goldenMul (⟨5, 0⟩ : GoldenInt) w).snd at hs
  simp only [goldenSub, goldenAdd, goldenNeg, goldenPhi, goldenOfInt, goldenMul,
    add_zero, neg_zero, zero_mul] at hs
  omega

section Quintic
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)

example : quinticPhi hζ = 1 + hζ.toInteger + hζ.toInteger ^ 4 := quinticPhi_eq hζ

-- Both directions retain the element, not only an absolute norm.
example (x : 𝓞 K) : quinticGoldenEquiv hζ ((quinticGoldenEquiv hζ).symm x) = x :=
  (quinticGoldenEquiv hζ).apply_symm_apply x

example (x : QuinticGoldenOrder) :
    (quinticGoldenEquiv hζ).symm (quinticGoldenEquiv hζ x) = x :=
  (quinticGoldenEquiv hζ).symm_apply_apply x

example (x : 𝓞 K) : quinticGoldenNorm hζ x =
    letI := quinticGoldenAlgebra hζ; Algebra.norm (DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt 1) x :=
  quinticGoldenNorm_eq_algebraNorm hζ x

-- Sum and difference phases have different golden signs.
example : fiveGoldenRelativeNorm hζ ((3 : 𝓞 K) + hζ.toInteger * (-2)) =
    goldenConj ⟨13, 6⟩ := by
  simpa using fiveGoldenRelativeNorm_phase hζ 3 (-2)

example : fiveGoldenRelativeNorm hζ ((3 : 𝓞 K) + hζ.toInteger * 2) =
    goldenConj ⟨13, -6⟩ := by
  simpa using fiveGoldenRelativeNorm_phase hζ 3 2

example : fiveGoldenRelativeNorm hζ (hζ.toInteger - 1) = goldenConj goldenTau :=
  fiveGoldenRelativeNorm_ramifier hζ

-- Relative norm cannot recover a phase: ζ and 1 have the same norm.
example : fiveGoldenRelativeNorm hζ hζ.toInteger = 1 ∧ hζ.toInteger ≠ 1 := by
  constructor
  · have h := fiveGoldenRelativeNorm_phase hζ 0 1
    calc
      _ = goldenConj ⟨1, 0⟩ := by simpa using h
      _ = 1 := by decide +kernel
  · exact hζ.toInteger_isPrimitiveRoot.ne_one (by decide)

-- λ-divisibility is much weaker than the integer mod-5 hypothesis of Kummer's lemma.
example : (hζ.toInteger - 1) ∣ (hζ.toInteger - 1) ∧
    ¬ (5 : 𝓞 K) ∣ hζ.toInteger - 1 := by
  refine ⟨dvd_refl _, ?_⟩
  intro h5
  have heq := quintic_rootOfUnity_eq_one_of_congruent hζ
    (x := hζ.toInteger) ⟨1, by decide, Or.inl (pow_one _).symm⟩ h5
  exact hζ.toInteger_isPrimitiveRoot.ne_one (by decide) heq

example (δ : (𝓞 K)ˣ) (h : ∃ n : ℤ, (5 : 𝓞 K) ∣ (δ : 𝓞 K) - (n : 𝓞 K)) :
    ∃ κ : (𝓞 K)ˣ, δ = κ ^ 5 := quintic_kummer_unit_power_criterion hζ δ h

example (x : 𝓞 K) (n : ℤ) (h : (5 : 𝓞 K) ∣ x - (n : 𝓞 K)) :
    (5 : GoldenInt) ∣ fiveGoldenRelativeNorm hζ x - (n : GoldenInt) ^ 2 :=
  fiveGoldenRelativeNorm_congruent_integer hζ h

example : Fintype.card (ClassGroup (𝓞 K)) = 1 := quintic_classGroup_card_eq_one
end Quintic

-- The exact same stripped element retains its norm and second coordinate.
example {u v w : ℕ} (q : SignedGoldenRamifierStrippedPacket u v w) :
    ∃ θ : GoldenInt, q.beta = θ ^ 5 ∧
      goldenNorm q.beta = (q.exceptional.powerSplit.b : ℤ) ^ 5 ∧
      q.beta.snd = -(5 : ℤ) ^ 7 * (q.exceptional.powerSplit.a : ℤ) ^ 10 := by
  obtain ⟨θ, hθ⟩ := exists_fifth_eq_stripped_beta_via_GN q
  exact ⟨θ, hθ, q.beta_norm, q.beta_snd⟩

example (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 := fermatFive_no_positive_solution_via_GN a b c ha hb hc

#print axioms DkMath.Lib.NumberTheory.quinticGoldenNorm_eq_algebraNorm
#print axioms DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion
#print axioms DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN
#print axioms DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN

run_cmd do
  for name in #[
    ``DkMath.Lib.NumberTheory.quintic_root_sum,
    ``DkMath.Lib.NumberTheory.quinticPhi,
    ``DkMath.Lib.NumberTheory.quinticPhi_eq,
    ``DkMath.Lib.NumberTheory.quinticPhi_sq,
    ``DkMath.Lib.NumberTheory.goldenCyclotomicEmbedding,
    ``DkMath.Lib.NumberTheory.quinticBasis,
    ``DkMath.Lib.NumberTheory.quinticBasis_apply,
    ``DkMath.Lib.NumberTheory.quinticCoordinates,
    ``DkMath.Lib.NumberTheory.quinticCoordinates_expansion,
    ``DkMath.Lib.NumberTheory.quinticGoldenA,
    ``DkMath.Lib.NumberTheory.quinticGoldenB,
    ``DkMath.Lib.NumberTheory.quinticGolden_expansion,
    ``DkMath.Lib.NumberTheory.quinticCoordinates_symm_apply,
    ``DkMath.Lib.NumberTheory.QuinticGoldenOrder,
    ``DkMath.Lib.NumberTheory.quinticGoldenToInteger,
    ``DkMath.Lib.NumberTheory.quinticGoldenToInteger_eq,
    ``DkMath.Lib.NumberTheory.quinticGoldenToInteger_bijective,
    ``DkMath.Lib.NumberTheory.quinticGoldenEquiv,
    ``DkMath.Lib.NumberTheory.quinticGoldenEquiv_algebraMap,
    ``DkMath.Lib.NumberTheory.quinticGoldenEquiv_omega,
    ``DkMath.Lib.NumberTheory.goldenCyclotomicEmbedding_injective,
    ``DkMath.Lib.NumberTheory.quinticGoldenNorm,
    ``DkMath.Lib.NumberTheory.quinticConj,
    ``DkMath.Lib.NumberTheory.quinticGoldenNorm_embedding,
    ``DkMath.Lib.NumberTheory.quinticGoldenEquiv_symm_embedding,
    ``DkMath.Lib.NumberTheory.quinticGoldenEquiv_symm_root,
    ``DkMath.Lib.NumberTheory.quinticGoldenNorm_phase,
    ``DkMath.Lib.NumberTheory.quinticGoldenNorm_ramifier,
    ``DkMath.Lib.NumberTheory.quinticConj_root,
    ``DkMath.Lib.NumberTheory.quinticConj_embedding,
    ``DkMath.Lib.NumberTheory.quinticGoldenAlgebra,
    ``DkMath.Lib.NumberTheory.quinticGoldenAlgEquiv,
    ``DkMath.Lib.NumberTheory.quinticGoldenNorm_eq_algebraNorm,
    ``DkMath.FLT.Kummer.fiveGoldenEmbedding,
    ``DkMath.FLT.Kummer.fiveGoldenRelativeNorm,
    ``DkMath.FLT.Kummer.fiveGoldenEmbedding_injective,
    ``DkMath.FLT.Kummer.fiveGoldenRelativeNorm_phase,
    ``DkMath.FLT.Kummer.fiveGoldenRelativeNorm_ramifier,
    ``DkMath.FLT.Kummer.fiveGoldenRelativeNorm_embedding,
    ``DkMath.FLT.Kummer.goldenConjRingEquiv,
    ``DkMath.FLT.Kummer.fiveGoldenRelativeNorm_congruent_integer,
    ``DkMath.FLT.Kummer.goldenUnit_of_isUnit,
    ``DkMath.FLT.Kummer.golden_unit_fifth_of_integer_congruence,
    ``DkMath.FLT.Kummer.quinticCoordinates_dvd_five,
    ``DkMath.FLT.Kummer.quinticCoordinates_root_pow,
    ``DkMath.FLT.Kummer.quinticCoordinates_pow,
    ``DkMath.FLT.Kummer.quinticCoordinates_root_four,
    ``DkMath.FLT.Kummer.quintic_rootOfUnity_eq_one_of_congruent,
    ``DkMath.FLT.Kummer.quinticConj_eq_CM,
    ``DkMath.FLT.Kummer.quintic_classGroup_card_eq_one,
    ``DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.exists_GN_quintic_factor_eq_zeta_sub_one_mul_fifth,
    ``DkMath.FLT.Kummer.five_dvd_result_of_stripped_coordinates,
    ``DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_of_coordinates,
    ``DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN_in,
    ``DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN,
    ``DkMath.FLT.Kummer.nonempty_gnGoldenZeroSectorCandidate,
    ``DkMath.FLT.Kummer.goldenZeroSectorDescentPacket_false_via_GN,
    ``DkMath.FLT.Kummer.signedGoldenRamifierStripped_false_via_GN,
    ``DkMath.FLT.Kummer.signedBranchARefuter_via_GN,
    ``DkMath.FLT.Kummer.counterexamplePack_false_via_GN,
    ``DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
