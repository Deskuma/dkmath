/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseResonantLift
import Mathlib.Algebra.Group.Units.Hom

#print "file: DkMath.FLT.FreyFiniteDecompositionAction"

/-! # 元の K 作用の忠実な有限群像
元の作用を単元へ持ち上げ、同じ作用核で割る。巡回性は結論しない。 -/
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

/-- 元の群表現が値を取る、元の線形 endomorphism の単元。 -/
def ResidualCyclicStage.kernelDecompositionUnits :
    A.decompositionSubgroup ℚ →* (Module.End ℤ (T.fixedH1CoefficientKernel A))ˣ :=
  (T.kernelDecompositionAction A hp5 hq hqp haddr hA).toHomUnits

/-- 単元への持ち上げは作用核を変更しない。 -/
theorem ResidualCyclicStage.kernelDecompositionUnits_ker :
    (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker = (T.kernelDecompositionAction A hp5 hq hqp haddr hA).ker := by
  ext σ
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- 元の同じ K 作用の実際の群像を表す作用核商。 -/
abbrev ResidualCyclicStage.finiteDecompositionImage :=
  (A.decompositionSubgroup ℚ) ⧸ (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker

/-- 元の同じ分解群から、その作用核商への標準射影。 -/
def ResidualCyclicStage.finiteDecompositionProjection :
    A.decompositionSubgroup ℚ →* T.finiteDecompositionImage A hp5 hq hqp haddr hA :=
  QuotientGroup.mk' _

/-- 作用核商は、元の線形自己同型の単元群に忠実に埋め込まれる。 -/
def ResidualCyclicStage.finiteDecompositionEmbedding :
    T.finiteDecompositionImage A hp5 hq hqp haddr hA →* (Module.End ℤ (T.fixedH1CoefficientKernel A))ˣ :=
  ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).range.subtype).comp (QuotientGroup.rangeKerLift (T.kernelDecompositionUnits A hp5 hq hqp haddr hA))

/-- 忠実性は同じ作用核による第一同型定理から従う。 -/
theorem ResidualCyclicStage.finiteDecompositionEmbedding_injective :
    Function.Injective (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) :=
  Subtype.val_injective.comp (QuotientGroup.rangeKerLift_injective (T.kernelDecompositionUnits A hp5 hq hqp haddr hA))

/-- 実際の K は有限なので、その作用核商も有限。 -/
instance ResidualCyclicStage.finiteDecompositionImage_finite : Finite (T.finiteDecompositionImage A hp5 hq hqp haddr hA) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  let : Finite (Module.End ℤ (T.fixedH1CoefficientKernel A)) :=
    Finite.of_injective (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) =>
      (z : T.fixedH1CoefficientKernel A → T.fixedH1CoefficientKernel A)) DFunLike.coe_injective
  exact Finite.of_injective (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) (T.finiteDecompositionEmbedding_injective A hp5 hq hqp haddr hA)
end
end DkMath.FLT.Frey.Source
