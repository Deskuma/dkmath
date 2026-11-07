/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFiniteDetector

#print "file: DkMathTest.FLT.FreyKernelFiniteDetector"

namespace FreyKernelFiniteDetectorTest
abbrev R := ZMod 5
private def pairing : (R × R) →ₗ[R] ((R × R) → R) where
  toFun x k := x.1 * k.1 + x.2 * k.2
  map_add' x y := by funext k; dsimp; ring
  map_smul' r x := by funext k; dsimp; ring

-- A common finite family separates even when NO single linear evaluation can.
private theorem pairing_injective : Function.Injective pairing := by
  intro x y he
  apply Prod.ext
  · simpa [pairing] using congrFun he (1, 0)
  · simpa [pairing] using congrFun he (0, 1)
example : LinearMap.ker pairing = ⊥ := LinearMap.ker_eq_bot.mpr pairing_injective
example (f : (R × R) →ₗ[R] R) : ¬ Function.Injective f := by
  intro hi
  have hc := Nat.card_le_card_of_injective f hi
  norm_num [Nat.card_prod, Nat.card_zmod] at hc

-- Genuine common quotient by the actual simultaneous kernel; cardinal25, not5.
private def commonQuotientEquiv : ((R × R) ⧸ LinearMap.ker pairing) ≃ₗ[R] (R × R) :=
  (LinearMap.ker pairing).quotEquivOfEqBot (LinearMap.ker_eq_bot.mpr pairing_injective)
example : Nat.card ((R × R) ⧸ LinearMap.ker pairing) = 25 := by
  rw [Nat.card_congr commonQuotientEquiv.toEquiv, Nat.card_prod, Nat.card_zmod]
example (x : R × R) : (5 : ℕ) • x = 0 := ZModModule.char_nsmul_eq_zero 5 x
example (x : R × R) : pairing x (1, 0) = x.1 := by simp [pairing]
example (x : R × R) : pairing x (0, 1) = x.2 := by simp [pairing]

-- Once an evaluation IS injective, its zero kernel and cardinal constraint are valid.
example : Function.Injective (LinearMap.id : R →ₗ[R] R) := fun _ _ he => he
example : Nat.card (LinearMap.ker (LinearMap.id : R →ₗ[R] R)) = 1 := by
  rw [LinearMap.ker_id]
  exact Nat.card_unique
end FreyKernelFiniteDetectorTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedEvaluation_image_card_dvd
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass_inflation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_fixedKernelTameFamily_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient_finite
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_separates
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation_card_dvd
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_finite_inertia_detector
#print axioms DkMath.FLT.Frey.Source.residual_exists_finitely_detected_coefficient_kernel
