/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure
import DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1

#print "file: DkMath.FLT.FreyContinuousKernelCharacters"

/-! # 実際の全係数核を連続指標へ埋め込む
既存の連続性と同じ具体的な γ の単一評価を使用する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の k の指標を、元の位相で連続な準同型として保持する。 -/
def ResidualCyclicStage.continuousKernelCharacter (k : T.fixedH1CoefficientKernel A) :
    ContinuousMonoidHom (inertiaSubgroupIn A ℚ) (Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  { T.fixedKernelCharacter A k with
    continuous_toFun := T.fixedKernelCharacter_continuous A hp5 hq hqp haddr hA k }

/-- 同じ連続指標の値は、元の評価値そのもの。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.continuousKernelCharacter A hp5 hq hqp haddr hA k σ) =
      T.fixedKernelEvaluation A σ k := rfl

/-- 同じ γ の評価で連続指標の埋め込みの単射性を得る。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_injective :
    Function.Injective (T.continuousKernelCharacter A hp5 hq hqp haddr hA) := by
  intro x y he
  apply T.generator_evaluation_injective A hp5 hq hqp haddr hA
  exact congrArg (fun f => Multiplicative.toAdd (f
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA))) he

/-- 同じ連続指標を通常 H¹ に忘却すると、元の核元の類を厳密に回収する。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_forget (k : T.fixedH1CoefficientKernel A) :
    ContinuousTrivialCharacterH1.forgetClass
      (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) = k.val := by
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)))).injective
  apply AddMonoidHom.ext
  intro σ
  exact ContinuousTrivialCharacterH1.forgetClass_evaluate
    (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) σ.toMul
end
end DkMath.FLT.Frey.Source

