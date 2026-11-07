/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FinitePrimePowerCharacter
import DkMath.FLT.FreyStageUpperQuotientTopology

#print "file: DkMath.FLT.FreyInertiaCharacterFiniteImage"

/-!
# 同じ慣性固定商への差分と有限像・開核の証明書

hclass と同じ Cofixed 候補から、正の p 冪指数の開核を内部構成する。
連続性・有限性・像の濃度を追加仮定にしない。非自明な coboundary の有限像であり、
非零 H¹ 類、野生慣性の消滅、Frobenius の q 倍則を主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.Algebra
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の同じ商作用について、全慣性群が固定する元の加法部分群。 -/
def ResidualCyclicStage.inertiaFixedUpperQuotient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup T.upperQuotient where
  carrier := {z | ∀ σ ∈ inertiaSubgroupIn A ℚ, T.upperQuotientAction σ z = z}
  zero_mem' := by intro σ _; exact map_zero _
  add_mem' := by intro x y hx hy σ hσ; rw [map_add, hx σ hσ, hy σ hσ]
  neg_mem' := by intro x hx σ hσ; rw [map_neg, hx σ hσ]

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 既存の同じ差分準同型の値域を、実際の慣性固定部分群へ制限する。 -/
def ResidualCyclicStage.inertiaFixedDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative (T.inertiaFixedUpperQuotient A) where
  toFun σ := Multiplicative.ofAdd ⟨Multiplicative.toAdd
    (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ), by
      intro τ hτ
      exact T.inertiaQuotientDifferenceCharacter_values_fixed hp5 hq hqp haddr A hA x ⟨τ, hτ⟩ σ⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x))
  map_mul' σ τ := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) σ τ)

/-- 値域制限後も、元の商の同じ値である。 -/
theorem ResidualCyclicStage.inertiaFixedDifferenceCharacter_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ)).val =
      Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) := rfl

/-- 同じ実際の商の濃度から、像・核商・核の指数を一つの p 冪に同定する。 -/
theorem ResidualCyclicStage.inertia_character_image_profile
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    let c := T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
    ∃ s ≤ n + 3, Nat.card c.range = p ^ s ∧
      Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  apply FinitePrimePowerCharacter.image_profile _ (Fact.out : p.Prime)
  exact T.upperQuotient_card

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害点を基点にすると、像と開核の指数は正の p 冪。 -/
theorem NarrowAbsorptionObstruction.inertia_character_finite_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    IsClopen (c.ker : Set (inertiaSubgroupIn A ℚ)) ∧
      ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card c.range = p ^ s ∧
        Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  refine ⟨T.inertiaQuotientDifferenceCharacter_kernel_isClopen hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩, ?_⟩
  exact FinitePrimePowerCharacter.nontrivial_image_profile _ (Fact.out : p.Prime)
    T.upperQuotient_card ⟨⟨τ, h.inertia⟩, (h.inertia_character_nontrivial hp5).1⟩

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
/-- 同じ hclass と Cofixed 候補から、非自明な有限像と正の p 冪指数の開核を内部供給する。 -/
theorem residual_exists_finite_inertia_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p ∧
      IsClopen (c.ker : Set (inertiaSubgroupIn A ℚ)) ∧
        ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card c.range = p ^ s ∧
          Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, (h.inertia_character_nontrivial hp5).1, (h.inertia_character_nontrivial hp5).2,
    h.inertia_character_finite_profile hp5⟩

end
end DkMath.FLT.Frey.Source
