/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalGeneratorCertificate

#print "file: DkMathTest.FLT.FreyRadicalGenerator"

namespace FreyRadicalGeneratorTest
abbrev R := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def rootMap : Multiplicative (R × R) →* Multiplicative R where
  toFun g := Multiplicative.ofAdd g.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl
private def otherMap : Multiplicative (R × R) →* Multiplicative R where
  toFun g := Multiplicative.ofAdd g.toAdd.2
  map_one' := rfl
  map_mul' _ _ := rfl
private def gamma : Multiplicative (R × R) := Multiplicative.ofAdd (1, 0)
private def epsilon : Multiplicative (R × R) := Multiplicative.ofAdd (0, 1)

-- A generator of one finite radical quotient does not generate an unrelated quotient.
example : rootMap gamma ≠ 1 := by decide
example : epsilon ∈ rootMap.ker := rfl
private theorem correction_visible : otherMap epsilon ≠ 1 := by decide
example : ¬ rootMap.ker ≤ otherMap.ker := by
  intro hi
  exact correction_visible (hi (show epsilon ∈ rootMap.ker from rfl))
example : otherMap gamma = 1 := rfl
example : otherMap (gamma ^ (0 : ℕ) * epsilon) ≠ 1 := by
  simpa only [pow_zero, one_mul] using correction_visible

-- Bounded powers leave the second coordinate as a real, visible correction.
example (a b : R) : (a, b) = a.val • ((1 : R), (0 : R)) + (0, b) := by
  apply Prod.ext
  · change a = a.val • (1 : R) + 0
    simp [nsmul_eq_mul]
  · simp
example (a : R) : a.val < 5 := a.val_lt

-- Coherent prime-power lifting retains exact order25; killing by5 would be false.
example : addOrderOf (1 : ZMod 25) = 5 ^ (1 + 1) :=
  addOrderOf_eq_prime_pow (by decide) (by decide)
example : (5 : ℕ) • (1 : ZMod 25) ≠ 0 := by decide
end FreyRadicalGeneratorTest

#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower
#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_zero
#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_succ_pow
#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat
#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow
#print axioms DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_ne_zero
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.radical
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.ratio
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.radical_ne_zero
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.ratio_pow
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.ratio_compat
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.ratio_eq_one_iff
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.valuation_prime_eq_one
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_val
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_pow
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_compat
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.exists_primitive_generator
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.generator
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.image_eq_pow_of_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.range_eq_zpowers_of_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.quotient_card_of_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.quotient_isCyclic_of_primitive
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.exists_generator_corrections
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_generator_stage_correction
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.radical_generator_error
#print axioms DkMath.FLT.Frey.Source.residual_exists_radical_generator_error
