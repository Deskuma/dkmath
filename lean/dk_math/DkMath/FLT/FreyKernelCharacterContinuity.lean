/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationConstraints

#print "file: DkMath.FLT.FreyKernelCharacterContinuity"

/-!
# 係数核の全ての元を元の有限捩れ差分で表し、連続性を回収する

通常 H¹ 全体の連続性は主張しない。実際の係数核 K の元だけを、既存の
Q/F≃K と二つの商写像の全射性により元の有限捩れ点へ戻す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ通常 H¹ 同型による、核の元 k に対応する準同型。 -/
def ResidualCyclicStage.fixedKernelCharacter (k : T.fixedH1CoefficientKernel A) :
    inertiaSubgroupIn A ℚ →* Multiplicative (T.inertiaFixedUpperQuotient A) where
  toFun σ := Multiplicative.ofAdd (T.fixedKernelEvaluation A σ k)
  map_one' := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom k.val |>.map_zero
  map_mul' σ τ := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom k.val |>.map_add
      (Additive.ofMul σ) (Additive.ofMul τ)

/-- 核指標の値は、以前構成した実際の評価値そのもの。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.fixedKernelCharacter A k σ) = T.fixedKernelEvaluation A σ k := rfl

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- K の任意の元は、元の有限捩れ点 x の同じ連結像で表せる。 -/
theorem ResidualCyclicStage.exists_torsion_fixedKernelElement (k : T.fixedH1CoefficientKernel A) :
    ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
      T.fixedCosetKernelElement hp5 hq hqp haddr A hA x = k := by
  obtain ⟨z, rfl⟩ := (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).surjective k
  obtain ⟨u, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  exact ⟨x, (T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA x).symm⟩

/-- 核元を有限捩れ点で表すと、指標全体が元の同じ固定差分指標になる。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedKernelCharacter A (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x := by
  apply MonoidHom.ext
  intro σ
  exact congrArg Multiplicative.ofAdd (T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ)

include hp5 hq hqp haddr hA in
/-- K の全ての元の指標は、元の Krull 部分群位相から連続である。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_continuous (k : T.fixedH1CoefficientKernel A) :
    Continuous (T.fixedKernelCharacter A k) := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  exact T.inertiaFixedDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

end
end DkMath.FLT.Frey.Source
