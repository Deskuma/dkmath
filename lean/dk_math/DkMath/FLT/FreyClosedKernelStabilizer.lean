/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantDecompositionLift
import DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup

#print "file: DkMath.FLT.FreyClosedKernelStabilizer"

/-! # 同じ実際の K の閉安定化部分群 -/
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

/-- 元の K 表現の、元 k の安定化部分群。 -/
def ResidualCyclicStage.kernelClosedStabilizer (k : T.fixedH1CoefficientKernel A) :
    Subgroup (A.decompositionSubgroup ℚ) :=
  ClosedFixedSubgroup.linearStabilizer (T.kernelDecompositionAction A hp5 hq hqp haddr hA) k

/-- 安定化群の閉性は、元の同じ γ の単射評価から得た閉固定条件そのもの。 -/
theorem ResidualCyclicStage.kernelClosedStabilizer_isClosed (k : T.fixedH1CoefficientKernel A) :
    IsClosed (T.kernelClosedStabilizer A hp5 hq hqp haddr hA k : Set (A.decompositionSubgroup ℚ)) :=
  T.kernelDecomposition_stabilizer_isClosed A hp5 hq hqp haddr hA k

/-- 元の実際の慣性群は各 k の安定化群に入る。 -/
theorem ResidualCyclicStage.inertia_le_kernelClosedStabilizer (k : T.fixedH1CoefficientKernel A) :
    A.inertiaSubgroup ℚ ≤ T.kernelClosedStabilizer A hp5 hq hqp haddr hA k := by
  intro σ hσ
  change T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k
  rw [show T.kernelDecompositionAction A hp5 hq hqp haddr hA σ = 1 from
    T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA hσ]
  rfl
end
end DkMath.FLT.Frey.Source
