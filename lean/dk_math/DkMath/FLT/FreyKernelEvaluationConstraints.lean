/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationCertificate

#print "file: DkMath.FLT.FreyKernelEvaluationConstraints"

/-!
# 実際の評価像の包含による指数制約

評価像 B は元の F の部分群。従って |B|=p^t, |F|=p^r なら t≤r。
同じ指数収支と合わせ、評価核の下界も得る。単一評価の単射性は仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 実際の評価像の濃度は、元の固定係数群 F の濃度を割る。 -/
theorem ResidualCyclicStage.fixedEvaluation_image_card_dvd (σ : inertiaSubgroupIn A ℚ) :
    Nat.card (LinearMap.range (T.fixedKernelEvaluation A σ)) ∣
      Nat.card (T.inertiaFixedUpperQuotient A) :=
  (LinearMap.range (T.fixedKernelEvaluation A σ)).toAddSubgroup.card_addSubgroup_dvd_card

variable {T A} {q : ℕ} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ三指数に t≤r と評価核の下界を加える。 -/
theorem NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
    ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ r ∧ u ≤ n + 1 ∧
      n + 3 - 2 * r ≤ u ∧ r + t + u = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨r, t, u, hr, hrb, ht, _, hu, hsum, hF, hB, hU, hK⟩ :=
    h.fixed_evaluation_balanced_profile hp5
  have hd := T.fixedEvaluation_image_card_dvd A ⟨τ, h.inertia⟩
  rw [hB, hF] at hd
  have htr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨r, t, u, hr, hrb, ht, htr, hu, by omega, hsum, hF, hB, hU, hK⟩

end
end DkMath.FLT.Frey.Source
