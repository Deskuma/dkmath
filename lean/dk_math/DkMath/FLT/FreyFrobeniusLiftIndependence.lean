/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseKernelFixed
import DkMath.Lib.NumberTheory.FrobeniusInertiaCoset

#print "file: DkMath.FLT.FreyFrobeniusLiftIndependence"

/-! # 実際の Frobenius 持ち上げの選択に依存しない作用と密度条件 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ}

/-- 二つの同じ q-Frobenius は元の D/I の同じ元を与える。 -/
theorem frobeniusResidueCoset_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    (φ : (A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) = ψ :=
  QuotientGroup.eq_iff_div_mem.mpr (ValuationFrobenius.frobenius_div_mem_inertia A φ ψ hφ hψ)

/-- 慣性と Frobenius が生成する元の部分群も、持ち上げによらない。 -/
theorem frobeniusInertiaJoin_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ = A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers ψ :=
  DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem _
    (ValuationFrobenius.frobenius_div_mem_inertia A φ ψ hφ hψ)

/-- 密度自体は明示条件だが、その条件は実際の Frobenius の選択によらない。 -/
theorem frobeniusInertia_dense_iff (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    ((A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) ↔
      ((A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers ψ).topologicalClosure = ⊤) := by
  rw [frobeniusInertiaJoin_eq A φ ψ hφ hψ]
end DkMath.FLT.Frey.Source
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

/-- 元の同じ F 上の作用は Frobenius の持ち上げの選択によらない。 -/
theorem ResidualCyclicStage.fixedFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.fixedDecompositionAction A φ = T.fixedDecompositionAction A ψ :=
  congrArg (T.fixedResidueAction A) (frobeniusResidueCoset_eq A φ ψ hφ hψ)

include hp5 hq hqp haddr hA
/-- 元の同じ E=Q/F 上の作用も選択によらない。 -/
theorem ResidualCyclicStage.quotientFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.quotientDecompositionAction A φ = T.quotientDecompositionAction A ψ :=
  congrArg (T.quotientResidueAction A hp5 hq hqp haddr hA) (frobeniusResidueCoset_eq A φ ψ hφ hψ)

/-- 元の同じ K 上の作用も選択によらない。 -/
theorem ResidualCyclicStage.kernelFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ = T.kernelDecompositionAction A hp5 hq hqp haddr hA ψ :=
  congrArg (T.kernelResidueAction A hp5 hq hqp haddr hA) (frobeniusResidueCoset_eq A φ ψ hφ hψ)
end
end DkMath.FLT.Frey.Source
