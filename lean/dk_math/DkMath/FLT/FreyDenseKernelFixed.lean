/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyClosedKernelStabilizer

#print "file: DkMath.FLT.FreyDenseKernelFixed"

/-! # 明示的な密度の下で、同じ核元の一元固定性から D 全体の固定性へ -/
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

/-- 密度条件の下で、同じ元の φ 固定性が hD を供給する。 -/
theorem ResidualCyclicStage.kernel_fixed_of_dense_join
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  have ht := ClosedFixedSubgroup.eq_top_of_dense_join (A.inertiaSubgroup ℚ)
    (T.kernelClosedStabilizer A hp5 hq hqp haddr hA k) φ
    (T.kernelClosedStabilizer_isClosed A hp5 hq hqp haddr hA k)
    (T.inertia_le_kernelClosedStabilizer A hp5 hq hqp haddr hA k) hfixed hdense
  intro σ
  change σ ∈ T.kernelClosedStabilizer A hp5 hq hqp haddr hA k
  rw [ht]
  exact Subgroup.mem_top σ

/-- 同じ密度入力の下で全 D 固定性は φ 固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_of_dense_join
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  ⟨fun h => h φ, T.kernel_fixed_of_dense_join A hp5 hq hqp haddr hA φ k hdense⟩
end
end DkMath.FLT.Frey.Source
