/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1PrimeOrder

#print "file: DkMath.FLT.FreyFixedConnectingInjective"

/-!
# 同じ固定係数の連結準同型の単射性

F=Q^I なので H⁰(Q)→H⁰(Q/F) は零。実際の長完全系列の正確性から δ は単射。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ係数射影が誘導する実際の通常の H⁰ 写像。 -/
abbrev ResidualCyclicStage.fixedH0Projection :=
  groupCohomology.map (A := T.fullInertiaCoefficient A) (B := T.fixedQuotientCoefficient A) (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientProjection A) 0

/-- Q の不変元は元の F に属するので、この同じ H⁰ 射影は零。 -/
theorem ResidualCyclicStage.fixedH0Projection_zero : T.fixedH0Projection A = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A))).injective
  change (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).hom
    (T.fixedH0Projection A z) = (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).hom 0
  rw [map_zero, groupCohomology.map_id_comp_H0Iso_hom_apply]
  apply Subtype.ext
  change (T.fixedCoefficientSubmodule A).mkQ
    ((groupCohomology.H0Iso (T.fullInertiaCoefficient A)).hom z).val = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  intro σ hσ
  exact ((groupCohomology.H0Iso (T.fullInertiaCoefficient A)).hom z).property ⟨σ, hσ⟩

/-- 同じ実際の H⁰→H¹ 連結準同型は単射。局所幾何や hclass は不要。 -/
theorem ResidualCyclicStage.fixedConnecting_injective : Function.Injective (T.fixedConnecting A) := by
  have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (groupCohomology.mapShortComplex₃_exact (T.fixedCoefficientSequence_shortExact A) (i := 0) rfl)
  change LinearMap.range (T.fixedH0Projection A).hom = LinearMap.ker (T.fixedConnecting A).hom at he
  have hr : LinearMap.range (T.fixedH0Projection A).hom = ⊥ := by
    rw [T.fixedH0Projection_zero]
    exact LinearMap.range_zero
  exact LinearMap.ker_eq_bot.mp (he.symm.trans hr)

end
end DkMath.FLT.Frey.Source
