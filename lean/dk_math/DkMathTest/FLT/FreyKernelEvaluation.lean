/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationCertificate

#print "file: DkMathTest.FLT.FreyKernelEvaluation"

namespace FreyKernelEvaluationTest
abbrev R := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ev : (R × R) →ₗ[R] R := LinearMap.fst R R R

-- A single nonzero evaluation need not be injective; all coordinates do separate.
example : ev (1, 0) = 1 := rfl
example : ev (0, 1) = 0 := rfl
example : ¬ Function.Injective ev := by
  intro hi
  have he := hi (show ev (0, 1) = ev 0 from rfl)
  have h10 : (1 : R) = 0 := congrArg Prod.snd he
  exact one_ne_zero h10
example (x y : R × R) (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := Prod.ext h1 h2

private def evKernelEquiv : R ≃ₗ[R] LinearMap.ker ev where
  toFun r := ⟨(0, r), rfl⟩
  invFun z := z.val.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    change (0, z.val.2) = z.val
    apply Prod.ext
    · exact (show z.val.1 = 0 from z.property).symm
    · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def evRangeEquiv : R ≃ₗ[R] LinearMap.range ev :=
  (LinearEquiv.ofTop (LinearMap.range ev) (by
    apply LinearMap.range_eq_top.mpr
    intro z
    exact ⟨(z, 0), rfl⟩)).symm

-- F and evaluation image each have order5, leaving a NONTRIVIAL evaluation kernel.
-- With n=0, r=t=u=1 attains both improved upper bounds s=n+2 and u=n+1.
example : Nat.card R = 5 := Nat.card_zmod 5
example : Nat.card (R × R) = 25 := by rw [Nat.card_prod, Nat.card_zmod]
example : Nat.card (R × (R × R)) = 5 ^ (0 + 3) := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  rfl
example : Nat.card (LinearMap.range ev) = 5 :=
  (Nat.card_congr evRangeEquiv.toEquiv).symm.trans (Nat.card_zmod 5)
example : Nat.card (LinearMap.ker ev) = 5 :=
  (Nat.card_congr evKernelEquiv.toEquiv).symm.trans (Nat.card_zmod 5)
private def sameImage : LinearMap.range ev := ⟨ev (1, 0), (1, 0), rfl⟩
example : sameImage.val = 1 := rfl
example : addOrderOf sameImage = 5 := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    change (5 : ℕ) • (1 : R) = 0
    decide
  · intro hz
    have h10 : (1 : R) = 0 := congrArg Subtype.val hz
    exact one_ne_zero h10
end FreyKernelEvaluationTest

#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_cyclic_card
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_fixed_card
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_positive_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_sharp_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_separates
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_card
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement_val
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile
#print axioms DkMath.FLT.Frey.Source.residual_exists_evaluated_coefficient_kernel
