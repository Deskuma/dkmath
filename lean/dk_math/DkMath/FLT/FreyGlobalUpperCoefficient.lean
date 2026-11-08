/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousObstructionCertificate
import DkMath.FLT.FreyStageUpperQuotientTopology

#print "file: DkMath.FLT.FreyGlobalUpperCoefficient"

/-! # 元の有限商 Q の大域表現と連続 coboundary
Q は全 Galois 群の係数である。局所固定係数 F を大域係数に取り替えない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の全 Galois 作用による同じ有限商 Q の整数線形表現。 -/
def ResidualCyclicStage.fullGlobalCoefficient : Rep ℤ (Field.absoluteGaloisGroup ℚ) := Rep.of
  { toFun := fun σ => (T.upperQuotientAction σ).toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro z
      change T.upperQuotientAction 1 z = z
      rw [map_one]
      rfl
    map_mul' := by
      intro σ τ
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z)
        (T.upperQuotientAction.map_mul σ τ) }

/-- 元の Q の商位相を大域表現の同じ台集合に保持する。 -/
instance ResidualCyclicStage.fullGlobalCoefficientTopology : TopologicalSpace T.fullGlobalCoefficient :=
  inferInstanceAs (TopologicalSpace T.upperQuotient)

/-- 同じ点の商類 [x] の大域 coboundary。 -/
def ResidualCyclicStage.fullGlobalCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.cocycles₁ T.fullGlobalCoefficient :=
  ⟨groupCohomology.d₀₁ T.fullGlobalCoefficient ((QuotientAddGroup.mk' T.upperStage) x),
    groupCohomology.d₀₁_apply_mem_cocycles₁ _⟩

/-- 大域 cocycle の値は元の全 Galois 作用差そのもの。 -/
theorem ResidualCyclicStage.fullGlobalCocycle_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : Field.absoluteGaloisGroup ℚ) :
    T.fullGlobalCocycle x σ = T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x := rfl

/-- 同じ Q の商位相で、元の Krull 位相から連続な大域代表。 -/
theorem ResidualCyclicStage.fullGlobalCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (fun σ : Field.absoluteGaloisGroup ℚ => (T.fullGlobalCocycle x σ : T.upperQuotient)) :=
  by
  change Continuous (fun σ : Field.absoluteGaloisGroup ℚ => T.upperQuotientAction σ
    ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x)
  exact (ResidualCyclicStage.upperQuotient_orbit_continuous T _).sub continuous_const

/-- この大域 Q 値の類は coboundary なので零。局所 F 値の類とは異なる。 -/
theorem ResidualCyclicStage.fullGlobalClass_zero
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x) = 0 := by
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  exact ⟨(QuotientAddGroup.mk' T.upperStage) x, rfl⟩
end
end DkMath.FLT.Frey.Source

