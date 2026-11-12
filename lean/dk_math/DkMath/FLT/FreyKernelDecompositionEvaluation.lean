/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingDecompositionEquivariance

#print "file: DkMath.FLT.FreyKernelDecompositionEvaluation"

/-! # 元の全係数核の分解群輸送と評価の共変性
輸送で不変になるとは仮定しない。同じ連続代表の値で作用を検証する。 -/
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

/-- 同じ核元の同じ評価は、D の作用と慣性共役に関して共変。 -/
theorem ResidualCyclicStage.kernelDecompositionEvaluation (σ : A.decompositionSubgroup ℚ)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
      T.fixedDecompositionAction A σ (T.fixedKernelEvaluation A
        ⟨σ.val⁻¹ * τ.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val τ.val σ.property τ.property⟩ k) := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.kernelDecompositionAction_coset A hp5 hq hqp haddr hA σ x]
  change T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ =
    T.fixedDecompositionAction A σ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x _)
  exact T.continuousCocycle_decomposition_conjugate A hp5 hq hqp haddr hA σ τ x

/-- 同じ具体的 γ での評価だけで、D 不変性を判定できる。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_generator_evaluation (σ : A.decompositionSubgroup ℚ)
    (k : T.fixedH1CoefficientKernel A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k ↔
    T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
      (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
    T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  ⟨fun h => congrArg _ h, fun he => T.generator_evaluation_injective A hp5 hq hqp haddr hA he⟩
end
end DkMath.FLT.Frey.Source

