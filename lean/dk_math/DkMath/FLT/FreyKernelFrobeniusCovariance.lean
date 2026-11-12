/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueDecompositionAction

#print "file: DkMath.FLT.FreyKernelFrobeniusCovariance"

/-! # 同じ全核指標での Frobenius q 倍公式
元の tame 商の実際の共役冪公式を、同じ固定基点の評価へ輸送する。 -/
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

/-- 任意の同じ核元の評価は、実際の Frobenius 共役で q 倍される。 -/
theorem ResidualCyclicStage.kernelEvaluation_frobenius_conjugate
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelEvaluation A
      ⟨φ.val * τ.val * φ.val⁻¹, decomposition_conj_mem_inertia A φ.val τ.val φ.property τ.property⟩ k =
      q • T.fixedKernelEvaluation A τ k := by
  obtain ⟨hc, he⟩ := tameInertia_frobenius_power A hφ τ
  have hv := congrArg (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k) he
  rw [map_pow] at hv
  exact congrArg Multiplicative.toAdd hv

/-- 輸送する核元と係数作用を同時に保った Frobenius 評価関係。 -/
theorem ResidualCyclicStage.kernelFrobenius_evaluation_relation
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    q • T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k) =
      T.fixedDecompositionAction A φ (T.fixedKernelEvaluation A τ k) := by
  let η : inertiaSubgroupIn A ℚ := ⟨φ.val * τ.val * φ.val⁻¹,
    decomposition_conj_mem_inertia A φ.val τ.val φ.property τ.property⟩
  have hc := T.kernelDecompositionEvaluation A hp5 hq hqp haddr hA φ η k
  have he : (⟨φ.val⁻¹ * η.val * φ.val, decomposition_inv_conj_mem_inertia A φ.val η.val φ.property η.property⟩ :
    inertiaSubgroupIn A ℚ) = τ := by
    apply Subtype.ext
    dsimp [η]
    group
  rw [he] at hc
  exact (T.kernelEvaluation_frobenius_conjugate A hp5 hq hqp haddr hA φ hφ τ _).symm.trans hc
end
end DkMath.FLT.Frey.Source

