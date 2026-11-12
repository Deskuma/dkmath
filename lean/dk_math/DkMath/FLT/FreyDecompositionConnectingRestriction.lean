/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionConnectingCocycle

#print "file: DkMath.FLT.FreyDecompositionConnectingRestriction"

/-! # D 上の連結類を同じ I 上の実際の類へ制限する
D 不変性を保持したまま、群包含・係数射・同じ代表を明示する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.ValuationInertia
/-- 元の全自己同型群内の慣性像から、同じ分解群への包含。 -/
def inertiaToDecomposition (A : ValuationSubring (AlgebraicClosure ℚ)) :
    inertiaSubgroupIn A ℚ →* A.decompositionSubgroup ℚ where
  toFun σ := ⟨σ.val, mem_decomposition_of_mem_inertia A σ.val σ.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ F の D 表現を I へ制限すると、元の自明係数に一致する。 -/
def ResidualCyclicStage.decompositionInertiaCoefficient :
    Rep.res (inertiaToDecomposition A) (T.fixedDecompositionCoefficient A) ⟶
      TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) :=
  Rep.ofHom ⟨LinearMap.id, fun σ => by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact z.property σ.val σ.property⟩

/-- 元の I⊆D に沿う、同じ F 係数での通常 H¹ 制限。 -/
def ResidualCyclicStage.decompositionInertiaRestriction :=
  groupCohomology.map (A := T.fixedDecompositionCoefficient A)
    (B := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (inertiaToDecomposition A) (T.decompositionInertiaCoefficient A) 1
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ D 連結 cocycle の制限は、元の同じ連続 I cocycle。 -/
theorem ResidualCyclicStage.decompositionCocycle_restrict
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.mapCocycles₁ (inertiaToDecomposition A) (T.decompositionInertiaCoefficient A)
      (T.decompositionConnectingCocycle A x hz) =
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA x := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  apply Subtype.ext
  exact (T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA x σ).symm

/-- 同じ点の D 上の類を制限すると、元の同じ核元の類を回収する。 -/
theorem ResidualCyclicStage.decompositionClass_restrict_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    T.decompositionInertiaRestriction A (groupCohomology.H1π _ (T.decompositionConnectingCocycle A x hz)) =
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val := by
  have he := groupCohomology.H1π_comp_map_apply (inertiaToDecomposition A)
    (T.decompositionInertiaCoefficient A) (T.decompositionConnectingCocycle A x hz)
  rw [T.decompositionCocycle_restrict A hp5 hq hqp haddr hA x hz,
    T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x] at he
  exact he.trans (T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x).symm
end
end DkMath.FLT.Frey.Source

