/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionConnectingRestriction

#print "file: DkMath.FLT.FreyResonantDecompositionLift"

/-! # 元の障害値の共鳴符号と、D 不変性の下での同じ類の持ち上げ
符号等式や D 不変性は供給しない。条件を明示して実際の D cocycle を構成する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の共鳴二分岐で、同じ厳密位数 p の値による判定を供給する。 -/
theorem NarrowAbsorptionObstruction.exists_prime_sign_frobenius_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧ addOrderOf v = p ∧
      (((q : ZMod p) = 1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
        T.fixedDecompositionAction A φ v = v)) ∨
       ((q : ZMod p) = -1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
        T.fixedDecompositionAction A φ v = -v))) := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  exact ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, h.generatorValue_order_eq_prime hp5,
    h.frobenius_fixed_resonant_signs hp5 _ hφ⟩

/-- 元の同じ障害核元が D 全体で固定される場合に限る、非零で連続な D 類の具体的持ち上げ。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hD : ∀ σ : A.decompositionSubgroup ℚ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
        T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ => (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  have hz (σ : A.decompositionSubgroup ℚ) : T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x) := by
    apply (T.kernel_fixed_iff_quotient_fixed A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ _).mp
    exact hD σ
  let c := T.decompositionConnectingCocycle A x hz
  have hr := T.decompositionClass_restrict_kernel A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over x hz
  refine ⟨c, T.decompositionConnectingCocycle_continuous A x hz, hr, ?_⟩
  intro hc
  rw [hc, map_zero] at hr
  apply (h.fixed_H1_nonzero hp5).2
  exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).symm.trans hr.symm
end
end DkMath.FLT.Frey.Source

