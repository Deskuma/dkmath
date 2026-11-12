/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionCocycleCovariance

#print "file: DkMath.FLT.FreyRelativeGlobalOrigin"

/-! # 同じ局所 F 障害の、係数を含めた相対的大域起源
大域 Q coboundary の制限と局所 F 非零類を同時に保持する。F 値の大域 Selmer 類は構成しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ連続 F cocycle の係数包含は、実際の大域 Q coboundary の制限に一致。 -/
theorem ResidualCyclicStage.continuousCocycle_global_origin
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.mapCocycles₁ (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A)
      (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
    groupCohomology.mapCocycles₁ (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A)
      (T.fullGlobalCocycle x) := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  exact T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA x σ

/-- 係数包含と群制限の両経路で、同じ通常 H¹ 類に到達する。 -/
theorem ResidualCyclicStage.continuousClass_global_origin_square
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
      (groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x)) =
      T.globalInertiaRestriction A (groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x)) := by
  have hl := groupCohomology.H1π_comp_map_apply (MonoidHom.id (inertiaSubgroupIn A ℚ))
    (T.fixedCoefficientInclusion A) (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x)
  have hr := groupCohomology.H1π_comp_map_apply (inertiaSubgroupIn A ℚ).subtype
    (T.globalInertiaCoefficient A) (T.fullGlobalCocycle x)
  exact hl.trans ((congrArg (fun c : groupCohomology.cocycles₁ (T.fullInertiaCoefficient A) =>
    groupCohomology.H1π (T.fullInertiaCoefficient A) c)
      (T.continuousCocycle_global_origin A hp5 hq hqp haddr hA x)).trans hr.symm)
end
end DkMath.FLT.Frey.Source

