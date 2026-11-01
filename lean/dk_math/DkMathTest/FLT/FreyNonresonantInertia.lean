/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia

namespace DkMathTest.FLT.FreyNonresonantInertia

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open DkMath.FLT.Frey.Source

-- A real higher cyclic level: on Z/25, multiplication by 2 is neither sign
-- on the 5-socle. Any subgroup receiving either sign difference must be the whole group.
example (H : AddSubgroup (ZMod 25))
    (hd : ∀ x : ZMod 25, x ∉ H → 2 • x - x ∈ H ∨ 2 • x + x ∈ H) : H = ⊤ := by
  apply top_unique
  apply CyclicSignSeparation.le_of_sub_or_add_mem (p := 5) (m := 2)
    (by decide) (⊤ : AddSubgroup (ZMod 25)) H
    (fun x _ => (by decide : ∀ x : ZMod 25, 5 ^ 2 • x = 0) x)
    (nsmulAddMonoidHom 2) (fun _ _ => AddSubgroup.mem_top _)
  · refine ⟨5, AddSubgroup.mem_top _, ?_⟩
    change 5 • (5 : ZMod 25) = 0 ∧ 2 • (5 : ZMod 25) ≠ 5
    decide
  · refine ⟨5, AddSubgroup.mem_top _, ?_⟩
    change 5 • (5 : ZMod 25) = 0 ∧ 2 • (5 : ZMod 25) ≠ -5
    decide
  · intro x _ hx
    exact hd x hx

-- Sign reversal is genuinely exceptional: its differences are nontrivial,
-- yet the sum always vanishes and does not force containment in the zero subgroup.
example : (∀ x : ZMod 5, (-AddMonoidHom.id (ZMod 5)) x + x ∈ (⊥ : AddSubgroup (ZMod 5))) ∧
    ¬ (⊤ : AddSubgroup (ZMod 5)) ≤ ⊥ := by
  constructor
  · intro x
    simp
  · intro h
    have hz : (1 : ZMod 5) = 0 := (AddSubgroup.mem_bot).mp (h (AddSubgroup.mem_top 1))
    exact (by decide : (1 : ZMod 5) ≠ 0) hz

example : (-AddMonoidHom.id (ZMod 5)) 1 ≠ (1 : ZMod 5) := by decide

-- Both exceptional classes really occur at prime addresses; no blanket elimination is valid.
example : (11 : ZMod 5) = 1 ∧ (19 : ZMod 5) = -1 := by decide
example : Nat.Prime 11 ∧ Nat.Prime 19 := by decide

-- A constructed arithmetic Frobenius, not an arbitrary action labelled Frobenius.
section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A 2) :
    ∃ σ : Field.absoluteGaloisGroup ℚ, ValuationFrobenius.IsFrobeniusAt A σ 2 ∧
      (CyclotomicRootModule.cyclotomicCharacter 5 σ : ZMod 5) = 2 := by
  obtain ⟨σ, hσ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  exact ⟨σ, hσ, CyclotomicFrobenius.cyclotomicCharacter_eq_natCast (p := 5)
    Nat.prime_two (by decide) A hA hσ⟩

end

#check cyclic_tower_eq_smooth_torsion_of_nonresonant
#check preimage_pointAction_sub_mem_of_nonresonant_bad
#check residual_preimage_unramified_away_of_resonant_inertia
#check residual_cofixed_tower_resonant_inertia_frobenius_impossible

#print axioms CyclotomicFrobenius.roots_eq_of_congruent
#print axioms CyclotomicFrobenius.apply_root_eq_pow
#print axioms CyclotomicFrobenius.cyclotomicCharacter_eq_natCast
#print axioms EllipticNodalDecomposition.defect_identity
#print axioms EllipticNodalDecomposition.centre_decomposition_fixed
#print axioms EllipticNodalDecomposition.sub_or_add_smooth_of_odd_torsion
#print axioms CyclicSignSeparation.le_of_sub_or_add_mem
#print axioms residual_cofixed_frobenius_sign_separated
#print axioms cyclic_tower_eq_smooth_torsion_of_nonresonant
#print axioms inertia_difference_smooth_at_bad_address
#print axioms prime_power_pointAction_sub_mem_of_nonresonant_bad
#print axioms preimage_pointAction_sub_mem_of_nonresonant_bad
#print axioms small_prime_sign_separated
#print axioms residual_preimage_unramified_away_of_resonant_inertia
#print axioms residual_cofixed_tower_resonant_inertia_frobenius_impossible

end DkMathTest.FLT.FreyNonresonantInertia
