/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameStructureCertificate

#print "file: DkMathTest.FLT.FreyCommonTameStructure"

namespace FreyCommonTameStructureTest
abbrev R := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- R1 does not supply R2: a finite abelian 5-group killed by5 can be noncyclic.
private theorem plane_card : Nat.card (Multiplicative (R × R)) = 25 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (R × R) ≃ R × R),
    Nat.card_prod, Nat.card_zmod]
example : IsPGroup 5 (Multiplicative (R × R)) := IsPGroup.of_card (show Nat.card (Multiplicative (R × R)) = 5 ^ 2 from plane_card)
private theorem plane_killed (g : Multiplicative (R × R)) : g ^ (5 : ℕ) = 1 := by
  change (5 : ℕ) • Multiplicative.toAdd g = 0
  exact ZModModule.char_nsmul_eq_zero 5 _
example : ¬ IsCyclic (Multiplicative (R × R)) := by
  intro hc
  let := hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Multiplicative (R × R))
  have hd := orderOf_dvd_of_pow_eq_one (plane_killed g)
  rw [hg, plane_card] at hd
  norm_num at hd

-- A genuine cyclic detector still permits a NONZERO K: r=2,s=1,n=0 is consistent.
example : IsCyclic (Multiplicative R) := inferInstance
private def single : R →ₗ[R] (R × R) where
  toFun k := (k, 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
example : Function.Injective single := by
  intro x y he
  exact congrArg Prod.fst he
example : (1 : R) ≠ 0 := one_ne_zero
example : Nat.card R * Nat.card (R × R) = 5 ^ (0 + 3) := by
  rw [Nat.card_prod, Nat.card_zmod]
  rfl

-- At the ACTUAL stage exponent125, power errors can be nontrivial in a prime-to5 part.
-- The identity of the projected common 5-quotient does not mean the inertia error is1.
example (a : ZMod 5) (b : ZMod 3) :
    Multiplicative.ofAdd (a, b) =
      (Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 3))) ^ a.val *
      (Multiplicative.ofAdd ((0 : ZMod 5), 2 * b)) ^ (5 ^ 3 : ℕ) * 1 ^ (5 ^ 3 : ℕ) := by
  change (a, b) = a.val • ((1 : ZMod 5), (0 : ZMod 3)) +
    (5 ^ 3 : ℕ) • ((0 : ZMod 5), 2 * b) + (5 ^ 3 : ℕ) • 0
  apply Prod.ext
  · change a = a.val • (1 : ZMod 5) + (5 ^ 3 : ℕ) • 0 + (5 ^ 3 : ℕ) • 0
    simp [nsmul_eq_mul]
  · change b = a.val • (0 : ZMod 3) + (5 ^ 3 : ℕ) • (2 * b) + (5 ^ 3 : ℕ) • 0
    norm_num [nsmul_eq_mul]
    have hm : (125 : ZMod 3) * 2 = 1 := by decide
    rw [← mul_assoc, hm, one_mul]
end FreyCommonTameStructureTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_mul_comm
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameCommGroup
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_value
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_card_dvd
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_isPGroup
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_exponent_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_projection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_one
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_quotient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generates_of_power_decomposition
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.common_isCyclic_of_power_decomposition
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.single_evaluation_of_power_decomposition
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_evaluation
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_ne_one
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonTame_positive_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic
#print axioms DkMath.FLT.Frey.Source.residual_exists_nontrivial_common_tame_pGroup
