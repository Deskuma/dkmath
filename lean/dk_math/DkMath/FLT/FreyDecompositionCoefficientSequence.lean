/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionOrbitContinuity

#print "file: DkMath.FLT.FreyDecompositionCoefficientSequence"

/-! # 同じ短完全列 0→F→Q→Q/F→0 を実際の D 上で構成する
F の D 安定性を内部証明から供給し、全 G 上へ拡張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の F の部分空間位相を同じ D 表現の台集合に保持する。 -/
instance ResidualCyclicStage.fixedDecompositionCoefficientTopology : TopologicalSpace (T.fixedDecompositionCoefficient A) :=
  inferInstanceAs (TopologicalSpace (T.inertiaFixedUpperQuotient A))

/-- 元の全 G の Q 係数を同じ D へ制限した表現。 -/
abbrev ResidualCyclicStage.fullDecompositionCoefficient : Rep ℤ (A.decompositionSubgroup ℚ) :=
  Rep.res (A.decompositionSubgroup ℚ).subtype T.fullGlobalCoefficient

/-- 元の同じ Q/F の D 表現。 -/
def ResidualCyclicStage.quotientDecompositionCoefficient : Rep ℤ (A.decompositionSubgroup ℚ) :=
  Rep.of (T.quotientDecompositionAction A)

/-- 同じ F→Q の D 同変な包含。 -/
def ResidualCyclicStage.decompositionCoefficientInclusion :
    T.fixedDecompositionCoefficient A ⟶ T.fullDecompositionCoefficient A :=
  Rep.ofHom ⟨(T.inertiaFixedUpperQuotient A).subtype.toIntLinearMap, fun _ => rfl⟩

/-- 同じ Q→Q/F の D 同変な商写像。 -/
def ResidualCyclicStage.decompositionCoefficientProjection :
    T.fullDecompositionCoefficient A ⟶ T.quotientDecompositionCoefficient A :=
  Rep.ofHom ⟨(T.fixedCoefficientSubmodule A).mkQ, fun _ => rfl⟩

/-- 同じ包含と商写像を持つ D 上の短複体。 -/
def ResidualCyclicStage.decompositionCoefficientSequence : ShortComplex (Rep ℤ (A.decompositionSubgroup ℚ)) :=
  ShortComplex.mk (T.decompositionCoefficientInclusion A) (T.decompositionCoefficientProjection A) (by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro z
    exact (Submodule.Quotient.mk_eq_zero _).mpr z.property)

attribute [local instance 2000] Rep.hV2
/-- 元の同じ係数による D 上の短完全性。 -/
theorem ResidualCyclicStage.decompositionCoefficientSequence_shortExact :
    (T.decompositionCoefficientSequence A).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((T.decompositionCoefficientSequence A).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ (A.decompositionSubgroup ℚ)) (ModuleCat ℤ))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    exact ⟨⟨z, (Submodule.Quotient.mk_eq_zero _).mp hz⟩, rfl⟩
  · exact (Rep.mono_iff_injective _).mpr Subtype.val_injective
  · exact (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
end
end DkMath.FLT.Frey.Source

