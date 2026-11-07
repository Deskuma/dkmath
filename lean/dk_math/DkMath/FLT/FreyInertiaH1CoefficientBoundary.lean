/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedInertiaH1
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

#print "file: DkMath.FLT.FreyInertiaH1CoefficientBoundary"

/-!
# 固定係数での非零性と元の実際の商加群での零性

F=Q^I の自明作用と、元の Q の実際の慣性作用を区別する。
同じ代表の F→Q による像は、同じ商元 [x] の作用差という coboundary になる。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の同じ商 Q の実際の慣性作用を、整数線形表現として読む。 -/
def ResidualCyclicStage.fullInertiaCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep ℤ (inertiaSubgroupIn A ℚ) := Rep.of
  { toFun := fun σ => (T.upperQuotientAction σ.val).toIntLinearMap
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
        (T.upperQuotientAction.map_mul (σ.val : Field.absoluteGaloisGroup ℚ) τ.val) }

/-- 同じ商元 [x] の実際の作用差を代表とする通常の cocycle。 -/
def ResidualCyclicStage.fullInertiaCocycle (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.cocycles₁ (T.fullInertiaCoefficient A) :=
  ⟨groupCohomology.d₀₁ (T.fullInertiaCoefficient A) ((QuotientAddGroup.mk' T.upperStage) x),
    groupCohomology.d₀₁_apply_mem_cocycles₁ _⟩

/-- 元の実際の Q 係数では、この同じ差分の通常の H¹ 類は零。 -/
theorem ResidualCyclicStage.fullInertiaClass_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) = 0 := by
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  exact ⟨(QuotientAddGroup.mk' T.upperStage) x, rfl⟩

/-- 自明作用の実際の固定係数 F から、元の実際の Q への表現の射。 -/
def ResidualCyclicStage.fixedCoefficientInclusion (A : ValuationSubring (AlgebraicClosure ℚ)) :
    TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) ⟶
      T.fullInertiaCoefficient A :=
  Rep.ofHom
    { toLinearMap := (T.inertiaFixedUpperQuotient A).subtype.toIntLinearMap
      isIntertwining' := by
        intro σ
        apply LinearMap.ext
        intro z
        change z.val = T.upperQuotientAction σ.val z.val
        exact (z.property σ.val σ.property).symm }

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 固定係数 cocycle の同じ値を F→Q で写すと、同じ実際の coboundary。 -/
theorem ResidualCyclicStage.fixedCocycle_include_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (TrivialCharacterH1.cocycle
      (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ).val =
      T.fullInertiaCocycle A x σ := by
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) =
    T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x
  exact T.inertiaQuotientDifferenceCharacter_coboundary hp5 hq hqp haddr A hA x σ

/-- 係数包含が通常の H¹ に誘導する実際の写像は、同じ固定係数類を零へ送る。 -/
theorem ResidualCyclicStage.fixedInertiaClass_map_zero
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
      (T.fixedInertiaH1Class hp5 hq hqp haddr A hA x) = 0 := by
  rw [fixedInertiaH1Class, TrivialCharacterH1.cohomologyClass,
    groupCohomology.H1π_comp_map_apply]
  have he : groupCohomology.mapCocycles₁ (MonoidHom.id (inertiaSubgroupIn A ℚ))
      (T.fixedCoefficientInclusion A)
      (TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)) =
      T.fullInertiaCocycle A x := by
    apply groupCohomology.cocycles₁_ext
    intro σ
    change (TrivialCharacterH1.cocycle
      (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ).val = _
    exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
  rw [he]
  exact T.fullInertiaClass_zero A x

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 同じ hclass と Cofixed 候補から、固定係数の非零 H¹ 類と元の係数への写像での零性を得る。 -/
theorem residual_exists_fixed_coefficient_H1
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      Continuous (T.fixedTameCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) ∧
      T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
        (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = 0 ∧
      groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) = 0 := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h,
    T.fixedTameCharacter_continuous hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    (h.fixed_H1_nonzero hp5).1, (h.fixed_H1_nonzero hp5).2,
    T.fixedInertiaClass_map_zero hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    T.fullInertiaClass_zero A ⟨y, h.killed⟩⟩

end
end DkMath.FLT.Frey.Source
