/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1Inflation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

#print "file: DkMath.FLT.FreyFixedCoefficientSequence"

/-!
# 元の実際の係数による短完全列 0→F→Q→Q/F→0

F=Q^I の元の部分群を整数部分加群と読み、元の慣性作用を商へ降ろす。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の同じ固定部分群を、元の Q の整数部分加群として読む。 -/
abbrev ResidualCyclicStage.fixedCoefficientSubmodule : Submodule ℤ (T.fullInertiaCoefficient A) :=
  (T.inertiaFixedUpperQuotient A).toIntSubmodule

/-- 同じ固定部分加群は元の実際の慣性作用で安定。 -/
theorem ResidualCyclicStage.fixedCoefficient_stable (σ : inertiaSubgroupIn A ℚ) :
    T.fixedCoefficientSubmodule A ≤ (T.fixedCoefficientSubmodule A).comap
      ((T.fullInertiaCoefficient A).ρ σ) := by
  intro z hz
  change T.upperQuotientAction σ.val z ∈ T.inertiaFixedUpperQuotient A
  rw [hz σ.val σ.property]
  exact hz

/-- 元の Q/F への実際の商表現。 -/
def ResidualCyclicStage.fixedQuotientCoefficient : Rep ℤ (inertiaSubgroupIn A ℚ) :=
  (T.fullInertiaCoefficient A).quotient (T.fixedCoefficientSubmodule A) (T.fixedCoefficient_stable A)

/-- 同じ点をその商類へ写す、元の実際の表現の射。 -/
def ResidualCyclicStage.fixedCoefficientProjection :
    T.fullInertiaCoefficient A ⟶ T.fixedQuotientCoefficient A :=
  (T.fullInertiaCoefficient A).mkQ (T.fixedCoefficientSubmodule A) (T.fixedCoefficient_stable A)

/-- 元の包含と商写像による実際の短複体。 -/
def ResidualCyclicStage.fixedCoefficientSequence : ShortComplex (Rep ℤ (inertiaSubgroupIn A ℚ)) :=
  ShortComplex.mk (T.fixedCoefficientInclusion A) (T.fixedCoefficientProjection A) (by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro z
    change (T.fixedCoefficientSubmodule A).mkQ z.val = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr z.property)

-- 任意の Rep オブジェクトでは、その記録済み整数加群構造を使う。
attribute [local instance 2000] Rep.hV2

/-- 元の包含は単射で、元の商写像は全射、像は同じ核。 -/
theorem ResidualCyclicStage.fixedCoefficientSequence_shortExact :
    (T.fixedCoefficientSequence A).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((T.fixedCoefficientSequence A).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ (inertiaSubgroupIn A ℚ)) (ModuleCat ℤ))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    have hz' : z ∈ T.fixedCoefficientSubmodule A := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨⟨z, hz'⟩, rfl⟩
  · apply (Rep.mono_iff_injective _).mpr
    exact Subtype.val_injective
  · apply (Rep.epi_iff_surjective _).mpr
    exact Submodule.mkQ_surjective _

end
end DkMath.FLT.Frey.Source
