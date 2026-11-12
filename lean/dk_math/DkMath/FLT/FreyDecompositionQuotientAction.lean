/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalObstructionCertificate

#print "file: DkMath.FLT.FreyDecompositionQuotientAction"

/-! # 同じ Q/F の分解群作用
元の F の D 安定性を使って商へ降ろす。F の全 G 安定性は仮定しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の Q/F 上の、同じ D の整数線形作用。 -/
def ResidualCyclicStage.quotientDecompositionAction :
    A.decompositionSubgroup ℚ →* Module.End ℤ (T.fixedQuotientCoefficient A) where
  toFun σ := (T.fixedCoefficientSubmodule A).mapQ (T.fixedCoefficientSubmodule A)
    (T.upperQuotientAction σ.val).toIntLinearMap (fun z hz => T.decomposition_preserves_fixed A σ ⟨z, hz⟩)
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
    exact congrArg (T.fixedCoefficientSubmodule A).mkQ
      (congrArg (fun f : AddMonoid.End T.upperQuotient => f v) T.upperQuotientAction.map_one)
  map_mul' σ τ := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
    exact congrArg (T.fixedCoefficientSubmodule A).mkQ
      (congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul σ.val τ.val))

/-- 商作用は元の同じ商写像と可換。 -/
theorem ResidualCyclicStage.quotientDecompositionAction_mk (σ : A.decompositionSubgroup ℚ) (v : T.upperQuotient) :
    T.quotientDecompositionAction A σ ((T.fixedCoefficientSubmodule A).mkQ v) =
      (T.fixedCoefficientSubmodule A).mkQ (T.upperQuotientAction σ.val v) := rfl

/-- 元の有限捩れ点を輸送した商類との一致。 -/
theorem ResidualCyclicStage.quotientDecompositionAction_coset (σ : A.decompositionSubgroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.quotientDecompositionAction A σ ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage)
        (ResidualCyclicStage.globalTranslateTorsion σ.val x)) := rfl
end
end DkMath.FLT.Frey.Source

