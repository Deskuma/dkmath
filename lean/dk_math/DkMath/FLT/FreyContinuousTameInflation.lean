/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousConnectingComparison

#print "file: DkMath.FLT.FreyContinuousTameInflation"

/-! # 元の連続 tame 指標と同じ通常 H¹ inflation
K の全ての元について連続代表を保持し、元の同じ I→I/W に沿う値と類を回収する。 -/
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

/-- 元の同じ商位相を持つ tame 指標を連続準同型として保持する。 -/
def ResidualCyclicStage.continuousKernelTameCharacter (k : T.fixedH1CoefficientKernel A) :
    ContinuousMonoidHom (tameInertiaQuotient A) (Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  { T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k with
    continuous_toFun := T.fixedKernelTameCharacter_continuous A hp5 hq hqp haddr hA k }

/-- 同じ I→I/W に沿う連続代表の値の一致。 -/
theorem ResidualCyclicStage.continuousKernelTameCharacter_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k (QuotientGroup.mk σ) =
      T.continuousKernelCharacter A hp5 hq hqp haddr hA k σ := rfl

/-- 連続 cocycle 自体の inflation における値も一致する。 -/
theorem ResidualCyclicStage.continuousKernelTameCocycle_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    ContinuousTrivialCharacterH1.cocycle (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k)
      (QuotientGroup.mk σ) =
    ContinuousTrivialCharacterH1.cocycle (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) σ := rfl

/-- 連続代表を忘却してから、同じ通常 H¹ inflation を取ると元の k を回収する。 -/
theorem ResidualCyclicStage.continuousKernelTameClass_inflation (k : T.fixedH1CoefficientKernel A) :
    T.fixedH1Inflation A (ContinuousTrivialCharacterH1.forgetClass
      (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k)) = k.val :=
  T.fixedKernelTameClass_inflation A hp5 hq hqp haddr hA k

/-- 連続 tame 指標への写像も同じ係数核全体で単射。 -/
theorem ResidualCyclicStage.continuousKernelTameCharacter_injective :
    Function.Injective (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA) := by
  intro x y he
  apply T.continuousKernelCharacter_injective A hp5 hq hqp haddr hA
  apply ContinuousMonoidHom.ext
  intro σ
  exact congrArg (fun f => f (QuotientGroup.mk σ)) he
end
end DkMath.FLT.Frey.Source

