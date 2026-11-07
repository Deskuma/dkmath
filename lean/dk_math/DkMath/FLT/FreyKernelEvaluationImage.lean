/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelEvaluation

#print "file: DkMath.FLT.FreyKernelEvaluationImage"

/-!
# 同じ慣性評価の像にある位数 p の元

評価写像の像・核は実際の整数部分加群を使う。元の障害元の評価は零でなく、
像の中でも厳密位数 p を保つ。ただし一つの評価が K 全体で単射とは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 第一同型定理による、同じ評価写像の実際の像と核の濃度積。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_card (σ : inertiaSubgroupIn A ℚ) :
    Nat.card (LinearMap.range (T.fixedKernelEvaluation A σ)) *
      Nat.card (LinearMap.ker (T.fixedKernelEvaluation A σ)) = Nat.card (T.fixedH1CoefficientKernel A) := by
  have hc := (LinearMap.ker (T.fixedKernelEvaluation A σ)).card_eq_card_quotient_mul_card
  have he := Nat.card_congr (T.fixedKernelEvaluation A σ).quotKerEquivRange.toEquiv
  rw [he] at hc
  exact (mul_comm _ _).trans hc.symm

variable {T A} {q : ℕ} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の核元を元の τ で評価すると、元の固定差分 d そのものになる。 -/
theorem NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      h.fixedDifference hp5 :=
  T.fixedKernelEvaluation_coset A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
    h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩

/-- 同じ核元を評価した、実際の像部分加群の元。 -/
def NarrowAbsorptionObstruction.fixedEvaluationImageElement
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    LinearMap.range (T.fixedKernelEvaluation A ⟨τ, h.inertia⟩) :=
  ⟨_, T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩, rfl⟩

/-- 実際の像で保持した元の値も、同じ固定差分 d。 -/
theorem NarrowAbsorptionObstruction.fixedEvaluationImageElement_val
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    (h.fixedEvaluationImageElement hp5).val = h.fixedDifference hp5 :=
  h.fixedKernelEvaluation_obstruction hp5

/-- 同じ評価像の元は、像部分加群の中でも厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    addOrderOf (h.fixedEvaluationImageElement hp5) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  have hd := addOrderOf_eq_prime_iff.mp (h.fixedDifference_order_eq_prime hp5)
  constructor
  · apply Subtype.ext
    change p • (h.fixedEvaluationImageElement hp5).val = 0
    rw [h.fixedEvaluationImageElement_val hp5]
    exact hd.1
  · intro hz
    apply hd.2
    exact (h.fixedEvaluationImageElement_val hp5).symm.trans (congrArg Subtype.val hz)

/-- 同じ評価の像全体の濃度は p で割れる。像全体の濃度が p とは限らない。 -/
theorem NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    p ∣ Nat.card (LinearMap.range (T.fixedKernelEvaluation A ⟨τ, h.inertia⟩)) := by
  have hd := addOrderOf_dvd_natCard (h.fixedEvaluationImageElement hp5)
  exact dvd_trans ((h.fixedEvaluationImage_order_eq_prime hp5).symm ▸ dvd_refl p) hd

end
end DkMath.FLT.Frey.Source
