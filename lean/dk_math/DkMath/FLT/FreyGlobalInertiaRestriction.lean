/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGlobalUpperCoefficient

#print "file: DkMath.FLT.FreyGlobalInertiaRestriction"

/-! # 同じ大域 Q 係数から元の慣性 Q 係数への制限
群と係数の両方を明示して同じ代表を回収する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 全 Galois 表現を元の慣性群へ制限した係数からの恒等射。 -/
def ResidualCyclicStage.globalInertiaCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep.res (inertiaSubgroupIn A ℚ).subtype T.fullGlobalCoefficient ⟶ T.fullInertiaCoefficient A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- 元の実際の慣性包含に沿う通常 H¹ 制限写像。 -/
def ResidualCyclicStage.globalInertiaRestriction (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.map (A := T.fullGlobalCoefficient) (B := T.fullInertiaCoefficient A)
    (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A) 1

/-- 同じ大域 coboundary の制限は、以前の同じ慣性 coboundary。 -/
theorem ResidualCyclicStage.globalCocycle_restrict (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.mapCocycles₁ (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A)
      (T.fullGlobalCocycle x) = T.fullInertiaCocycle A x := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  rfl

/-- 通常 H¹ 制限も、元の同じ代表の類を回収する。 -/
theorem ResidualCyclicStage.globalClass_restrict (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.globalInertiaRestriction A (groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x)) =
      groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) := by
  unfold globalInertiaRestriction
  have he := groupCohomology.H1π_comp_map_apply
    (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A) (T.fullGlobalCocycle x)
  rw [T.globalCocycle_restrict A x] at he
  exact he
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の連続 F 値代表を Q に含めた値は、同じ大域代表の慣性制限。 -/
theorem ResidualCyclicStage.continuousCocycle_global_restriction
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x σ).val = T.fullGlobalCocycle x σ.val := by
  rw [T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x]
  exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
end
end DkMath.FLT.Frey.Source

