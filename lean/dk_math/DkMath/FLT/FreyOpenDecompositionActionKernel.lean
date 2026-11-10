/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteDecompositionAction
import Mathlib.Topology.Algebra.Group.Quotient

#print "file: DkMath.FLT.FreyOpenDecompositionActionKernel"

/-! # 同じ γ の評価と有限性による作用核の開性
K に新たな位相を仮定せず、元の F 値連続軌道だけを用いる。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の K の各元を固定する条件は開集合でもある。 -/
theorem ResidualCyclicStage.kernelDecomposition_stabilizer_isOpen (k : T.fixedH1CoefficientKernel A) :
    IsOpen {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
  have he : {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} =
      {σ | T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
        (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
        T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k} := by
    ext σ
    exact T.kernel_fixed_iff_generator_evaluation A hp5 hq hqp haddr hA σ k
  rw [he]
  exact (isOpen_discrete {T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k}).preimage
    (T.kernelDecomposition_orbit_evaluation_continuous A hp5 hq hqp haddr hA k
      (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA))

/-- 同じ作用核は、有限個の元の開固定条件の共通部分。 -/
theorem ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen :
    IsOpen ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker : Set (A.decompositionSubgroup ℚ)) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  have he : ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker : Set (A.decompositionSubgroup ℚ)) =
      ⋂ k : T.fixedH1CoefficientKernel A,
        {σ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
    ext σ
    simp only [Set.mem_iInter]
    change (T.kernelDecompositionUnits A hp5 hq hqp haddr hA) σ = 1 ↔
      ∀ k, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k
    constructor
    · intro h k
      exact congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (congrArg Units.val h)
    · intro h
      apply Units.ext
      exact LinearMap.ext h
  rw [he]
  exact isOpen_iInter_of_finite (fun k => T.kernelDecomposition_stabilizer_isOpen A hp5 hq hqp haddr hA k)

/-- 同じ作用核商の元の商位相は離散。 -/
instance ResidualCyclicStage.finiteDecompositionImage_discrete :
    DiscreteTopology (T.finiteDecompositionImage A hp5 hq hqp haddr hA) :=
  QuotientGroup.discreteTopology (T.kernelDecompositionUnits_kernel_isOpen A hp5 hq hqp haddr hA)

/-- 元の同じ実際の慣性は、有限作用射影の核に入る。 -/
theorem ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel :
    A.inertiaSubgroup ℚ ≤ (T.finiteDecompositionProjection A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  apply (QuotientGroup.eq_one_iff σ).mpr
  rw [T.kernelDecompositionUnits_ker A hp5 hq hqp haddr hA]
  exact T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA hσ
end
end DkMath.FLT.Frey.Source
