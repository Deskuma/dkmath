/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenKummerUnit

#print "file: DkMathTest.FLT.Kummer.SevenConjugatePhase"

namespace DkMathTest.FLT.Kummer.SevenConjugatePhase

open scoped NumberField
open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

-- The concrete involution really sends the oriented root to its inverse.
example : integralEquiv (integralConj septicRoot_spec.toInteger) =
    SevenCyclotomicDegreeSixInt.zeta ^ 6 := by
  rw [integralEquiv_conj, integralEquiv_septicRoot,
    ← SevenCyclotomicDegreeSixInt.zetaInv_eq_pow_six]
  ext <;> simp [SevenCyclotomicDegreeSixInt.zeta, SevenCyclotomicDegreeSixInt.zetaInv]

-- Every nontrivial signed phase fails the full mod 7 congruence.
example (r : ℕ) (hr : 0 < r) (hr7 : r < 7) :
    ¬ (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ septicRoot_spec.toInteger ^ r - 1 := by
  intro hd
  have hp := septic_rootOfUnity_eq_one_of_congruent ⟨r, hr7, Or.inl rfl⟩ hd
  have hdiv := septicRoot_spec.toInteger_isPrimitiveRoot.dvd_of_pow_eq_one r hp
  omega

example (r : ℕ) (hr7 : r < 7) :
    ¬ (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ -septicRoot_spec.toInteger ^ r - 1 := by
  intro hd
  have hp := septic_rootOfUnity_eq_one_of_congruent ⟨r, hr7, Or.inr rfl⟩ hd
  have he : septicRoot_spec.toInteger ^ r = -1 := by linear_combination -hp
  have hh := congrArg (fun x : 𝓞 (CyclotomicField 7 ℚ) => x ^ 7) he
  rw [← pow_mul, Nat.mul_comm r 7, pow_mul,
    septicRoot_spec.toInteger_isPrimitiveRoot.pow_eq_one] at hh
  norm_num at hh

example (u : (𝓞 (CyclotomicField 7 ℚ))ˣ) : IsOfFinOrder (conjugateRatio u) :=
  conjugateRatio_finite u

example (u : (𝓞 (CyclotomicField 7 ℚ))ˣ)
    (h : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (n : _)) :
    conjugateRatio u = 1 := conjugateRatio_eq_one u h

-- A concrete primary unit, independent of a hypothetical Fermat solution.
-- alpha^7 = -25 + 14 alpha + 56 alpha^2, hence congruent to 3.
example : ∃ v : SevenCyclotomicDegreeSixInt.Ringˣ,
    (Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom
      SevenRealCubicInt.alphaUnit) ^ 7 = v ^ 7 := by
  apply concrete_kummer_unit_power_criterion
  refine ⟨3, (⟨⟨-4, 2, 8⟩, 0⟩ : SevenCyclotomicDegreeSixInt.Ring), ?_⟩
  change SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha ^ 7 - 3 =
    7 * (⟨⟨-4, 2, 8⟩, 0⟩ : SevenCyclotomicDegreeSixInt.Ring)
  decide +kernel

-- The recovery formula works for all odd degrees, including the next two primes.
example {G : Type*} [CommGroup G] {u v : G} (h : u ^ 2 = v ^ 11) :
    (u * v⁻¹ ^ 5) ^ 11 = u := DkMath.Lib.Algebra.oddPower_root_of_square 5 h
example {G : Type*} [CommGroup G] {u v : G} (h : u ^ 2 = v ^ 13) :
    (u * v⁻¹ ^ 6) ^ 13 = u := DkMath.Lib.Algebra.oddPower_root_of_square 6 h

#print axioms conjugateRatio_eq_one
#print axioms septic_kummer_unit_power_criterion
#print axioms GN_primary_unit_seventh
#print axioms exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh

run_cmd do
  for n in #[``DkMath.Lib.Algebra.oddPower_root_of_square,
      ``septicRoot,
      ``septicRoot_spec,
      ``septicRoot_toInteger,
      ``integralEquiv_septicRoot,
      ``septicBasis,
      ``septicBasis_apply,
      ``septicCoordinates,
      ``septicCoordinates_dvd_seven,
      ``septicCoordinates_root_pow,
      ``septicCoordinates_pow,
      ``septic_root_sum,
      ``septicCoordinates_root_six,
      ``septic_rootOfUnity_eq_one_of_congruent,
      ``integralConj,
      ``integralEquiv_conj,
      ``integralConj_root,
      ``integralConj_eq_CM,
      ``conjugateRatio,
      ``unit_square_eq_norm_mul_ratio,
      ``conjugateRatio_finite,
      ``conjugateRatio_congruent_one,
      ``conjugateRatio_eq_one,
      ``primary_unit_fixed,
      ``concrete_primary_unit_fixed,
      ``concrete_kummer_unit_power_criterion,
      ``septic_kummer_unit_power_criterion,
      ``GN_primary_unit_seventh,
      ``GN_factor_eq_zeta_sub_one_mul_seventh,
      ``septic_classGroup_card_eq_one,
      ``exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.SevenConjugatePhase
