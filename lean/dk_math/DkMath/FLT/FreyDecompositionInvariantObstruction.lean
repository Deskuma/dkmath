/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFrobeniusFixedCriterion

#print "file: DkMath.FLT.FreyDecompositionInvariantObstruction"

/-! # 同じ障害の輸送と不変性を、同じ Q/F と単一評価で判定する
不変性や大域 F 類の存在は仮定しない。新たな hclass を供給したとは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ核元が D で固定されることは、元の同じ剰余類の固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_quotient_fixed (σ : A.decompositionSubgroup ℚ)
    (z : T.fixedQuotientCoefficient A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
        T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z ↔
    T.quotientDecompositionAction A σ z = z := by
  rw [T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA]
  exact (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).injective.eq_iff
end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害核元の Frobenius 不変性を、同じ γ の一つの値だけで判定する。 -/
theorem NarrowAbsorptionObstruction.frobenius_fixed_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k :=
  T.kernelFrobenius_fixed_iff A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ hφ _
/-- 元の q 上の住所から実際の Frobenius を内部選択し、同じ障害の判定条件を供給する。 -/
theorem NarrowAbsorptionObstruction.exists_frobenius_fixed_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧
      T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k ≠ 0 ∧
      (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
       T.fixedDecompositionAction A φ
         (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) =
       q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  refine ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, ?_, h.frobenius_fixed_criterion hp5 _ hφ⟩
  intro he
  have hk := T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
    (show T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) 0 by
        simpa only [map_zero] using he)
  have hv := congrArg Subtype.val hk
  apply (h.fixed_H1_nonzero hp5).2
  exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).symm.trans hv
end
end DkMath.FLT.Frey.Source

