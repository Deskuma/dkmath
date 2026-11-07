/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelCharacterContinuity

#print "file: DkMath.FLT.FreyKernelTameDescent"

/-!
# 実際の係数核全体の野生零性・馴分岐降下・通常 H¹ inflation

一つの障害類だけでなく K の任意の元を、同じ野生合同部分群 W で割った J=I/W へ降ろす。
W と標準的な野生慣性との同定や J の procyclic 性は使わない。
-/
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

/-- K の全ての指標は、以前の同じ野生合同部分群上で零になる。 -/
theorem ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel (k : T.fixedH1CoefficientKernel A) :
    wildInertiaSubgroup A ≤ (T.fixedKernelCharacter A k).ker := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  exact T.wildInertia_le_fixed_character_kernel hp5 hq hqp haddr A hA x

/-- 任意の同じ核元の指標を、元の実際の商 J=I/W へ降ろす。 -/
def ResidualCyclicStage.fixedKernelTameCharacter (k : T.fixedH1CoefficientKernel A) :
    tameInertiaQuotient A →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift (wildInertiaSubgroup A) (T.fixedKernelCharacter A k)
    (T.wild_le_fixedKernelCharacter_kernel A hp5 hq hqp haddr hA k)

/-- 商に降ろしても、同じ慣性元における同じ値を保持する。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k (QuotientGroup.mk σ) =
      T.fixedKernelCharacter A k σ := rfl

/-- K の全ての降下指標は、同じ標準商位相から連続。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_continuous (k : T.fixedH1CoefficientKernel A) :
    Continuous (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k) := by
  apply continuous_quot_lift
  exact T.fixedKernelCharacter_continuous A hp5 hq hqp haddr hA k

/-- 元の有限捩れ点で表された場合、以前の同じ馴分岐指標を回収する。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedKernelTameCharacter A hp5 hq hqp haddr hA
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      T.fixedTameCharacter hp5 hq hqp haddr A hA x := by
  apply MonoidHom.ext
  intro t
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
  change T.fixedKernelCharacter A _ σ = _
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  rfl

/-- 全ての核元に対する、降下指標の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedKernelTameClass (k : T.fixedH1CoefficientKernel A) :=
  TrivialCharacterH1.cohomologyClass (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k)

/-- 同じ実際の inflation が、任意の同じ核元の値を回収する。 -/
theorem ResidualCyclicStage.fixedKernelTameClass_inflation (k : T.fixedH1CoefficientKernel A) :
    T.fixedH1Inflation A (T.fixedKernelTameClass A hp5 hq hqp haddr hA k) = k.val := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  unfold fixedKernelTameClass
  rw [T.fixedKernelTameCharacter_coset A hp5 hq hqp haddr hA x]
  exact (T.fixedTameClass_inflation hp5 hq hqp haddr A hA x).trans
    (T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x).symm

end
end DkMath.FLT.Frey.Source
