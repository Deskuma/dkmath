/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFiniteActionFactor
import DkMath.FLT.FreyFiniteImageFixedCriterion
import DkMath.FLT.FreyFrobeniusLiftIndependence

#print "file: DkMath.FLT.FreyKernelOrbitCriterion"

/-! # 同じ障害核元ひとつの有限軌道による判定
K 全体の有限作用像の生成より弱い条件を、元の作用で表す。 -/
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

/-- 特定の k に限った D 軌道が、同じ Frobenius の非負冪軌道に含まれる条件。 -/
def ResidualCyclicStage.KernelOrbitGenerated
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A) : Prop :=
  ∀ σ : A.decompositionSubgroup ℚ, ∃ m : ℕ,
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k =
      (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ ^ m) k

/-- K 全体の有限作用像生成は、各 k の軌道生成を与える。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_of_finite_image
    (φ : A.decompositionSubgroup ℚ)
    (himage : ∀ σ : A.decompositionSubgroup ℚ,
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈
        Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ))
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k := by
  intro σ
  obtain ⟨m, _, hm⟩ := T.finiteDecomposition_bounded_action_power A hp5 hq hqp haddr hA φ himage σ
  exact ⟨m, congrArg (fun f : Module.End ℤ (T.fixedH1CoefficientKernel A) => f k) hm⟩

/-- 同じ q-Frobenius の持ち上げを替えても、この k の軌道条件は変わらない。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_frobenius_iff
    (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k ↔
      T.KernelOrbitGenerated A hp5 hq hqp haddr hA ψ k := by
  unfold ResidualCyclicStage.KernelOrbitGenerated
  rw [T.kernelFrobenius_action_eq A hp5 hq hqp haddr hA φ ψ hφ hψ]

/-- Frobenius が同じ k を固定し、その軌道が生成されれば D 全体が k を固定する。 -/
theorem ResidualCyclicStage.kernel_fixed_of_orbit
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k)
    (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  let f : Module.End ℤ (T.fixedH1CoefficientKernel A) :=
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ
  have hp : ∀ m : ℕ, (f ^ m) k = k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      calc (f ^ (m + 1)) k = (f ^ m) (f k) :=
            congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (pow_succ f m)
        _ = (f ^ m) k := congrArg (fun z : T.fixedH1CoefficientKernel A => (f ^ m) z) hfixed
        _ = k := ih
  intro σ
  obtain ⟨m, hm⟩ := horbit σ
  exact hm.trans (hp m)

/-- 同じ k の D 固定性は、軌道条件の下で単一 Frobenius 固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_frobenius_of_orbit
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  ⟨fun h => h φ, T.kernel_fixed_of_orbit A hp5 hq hqp haddr hA φ k horbit⟩

/-- 軌道条件の下で元の γ による Frobenius 固有値判定を得る。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_eigenvalue_of_orbit
    (φ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (T.kernel_fixed_iff_frobenius_of_orbit A hp5 hq hqp haddr hA φ k horbit).trans
    (T.kernelFrobenius_fixed_iff A hp5 hq hqp haddr hA φ hφ k)

end
end DkMath.FLT.Frey.Source
