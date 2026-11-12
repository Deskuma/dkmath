/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionCoefficientSequence

#print "file: DkMath.FLT.FreyDecompositionConnectingCocycle"

/-! # D 不変な同じ剰余類に対する、実際の F 値連結 cocycle
D 不変性は明示条件。存在を仮定した大域 Selmer provider へ置き換えない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ短完全列の D 上の連結写像。 -/
abbrev ResidualCyclicStage.decompositionConnecting :=
  groupCohomology.δ (T.decompositionCoefficientSequence_shortExact A) 0 1 rfl

/-- 元の同じ点の商類が D 不変である場合の H⁰ 元。 -/
def ResidualCyclicStage.decompositionCosetH0
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :=
  (groupCohomology.H0Iso (T.quotientDecompositionCoefficient A)).inv
    ⟨(T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x), hz⟩

/-- D 不変剰余類の持ち上げの作用差は、元の F に属する。 -/
theorem ResidualCyclicStage.decomposition_difference_mem_fixed
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x))
    (σ : A.decompositionSubgroup ℚ) :
    T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x ∈ T.inertiaFixedUpperQuotient A := by
  apply (Submodule.Quotient.mk_eq_zero (T.fixedCoefficientSubmodule A)).mp
  change (T.fixedCoefficientSubmodule A).mkQ
    (T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x) = 0
  exact ((T.fixedCoefficientSubmodule A).mkQ.map_sub _ _).trans (sub_eq_zero.mpr (hz σ))

/-- D 不変性から実際の作用差を F 値 cocycle として構成する。 -/
def ResidualCyclicStage.decompositionConnectingCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A) :=
  ⟨fun σ => ⟨_, T.decomposition_difference_mem_fixed A x hz σ⟩,
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun σ τ => by
      apply Subtype.ext
      let g : Field.absoluteGaloisGroup ℚ := σ.val
      let t : Field.absoluteGaloisGroup ℚ := τ.val
      let v : T.upperQuotient := (QuotientAddGroup.mk' T.upperStage) x
      change T.upperQuotientAction (g * t) v - v =
        T.upperQuotientAction g (T.upperQuotientAction t v - v) + (T.upperQuotientAction g v - v)
      have hm : T.upperQuotientAction (g * t) v = T.upperQuotientAction g (T.upperQuotientAction t v) :=
        congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul g t)
      calc T.upperQuotientAction (g * t) v - v
          = T.upperQuotientAction g (T.upperQuotientAction t v) - v := congrArg (fun z => z - v) hm
        _ = (T.upperQuotientAction g (T.upperQuotientAction t v) - T.upperQuotientAction g v) +
            (T.upperQuotientAction g v - v) := by abel
        _ = T.upperQuotientAction g (T.upperQuotientAction t v - v) + (T.upperQuotientAction g v - v) :=
          congrArg (fun z => z + (T.upperQuotientAction g v - v)) ((T.upperQuotientAction g).map_sub _ _).symm)⟩

/-- 元の F の部分空間位相に関して、この D cocycle は連続。 -/
theorem ResidualCyclicStage.decompositionConnectingCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    Continuous (fun σ : A.decompositionSubgroup ℚ =>
      (T.decompositionConnectingCocycle A x hz σ : T.inertiaFixedUpperQuotient A)) := by
  change Continuous (fun σ : A.decompositionSubgroup ℚ =>
    (⟨T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x, T.decomposition_difference_mem_fixed A x hz σ⟩ : T.inertiaFixedUpperQuotient A))
  have hc : Continuous (fun σ : A.decompositionSubgroup ℚ =>
      T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x) :=
    ((T.upperQuotient_orbit_continuous _).comp
      (continuous_subtype_val : Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (σ.val : Field.absoluteGaloisGroup ℚ)))).sub continuous_const
  exact hc.subtype_mk _

/-- 同じ D cocycle の類は、元の同じ D 上の δ₀ の像。 -/
theorem ResidualCyclicStage.decompositionConnectingCocycle_class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.H1π _ (T.decompositionConnectingCocycle A x hz) =
      T.decompositionConnecting A (T.decompositionCosetH0 A x hz) := by
  symm
  exact groupCohomology.δ₀_apply (T.decompositionCoefficientSequence_shortExact A)
    ⟨(T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x), hz⟩
    ((QuotientAddGroup.mk' T.upperStage) x) rfl
    (T.decompositionConnectingCocycle A x hz) rfl
end
end DkMath.FLT.Frey.Source

