/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction
import DkMath.FLT.FreyStageUpperQuotient
import DkMath.Lib.NumberTheory.EllipticNodalUnipotence
import DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter

#print "file: DkMath.FLT.FreyInertiaDifferenceCharacter"

/-!
# 同じ慣性差分から通常の非自明な商値準同型へ

局所積零性を内部供給する。値は慣性固定、証人での商値は厳密位数 p。
Frobenius 共役を q 倍と同定したり、野生慣性を消去したりしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

section Local
variable (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
local notation "irep" => MonoidHom.comp (representation S.rationalCurve (p ^ (n + 1)))
  (Subgroup.subtype (inertiaSubgroupIn A ℚ))
include hp5 hq hqp haddr hA

/-- 同じ慣性群の任意の二元についての、実際の有限捩れ差分の積零性。 -/
theorem prime_power_inertia_difference_product_zero (σ τ : inertiaSubgroupIn A ℚ) :
    (irep σ - 1) * (irep τ - 1) = 0 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  exact EllipticNodalUnipotence.inertia_difference_product_zero S.rationalCurve _ A
    (S.valuationModel A) (S.valuationModel_map A) C D
    (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) σ.val τ.val σ.property τ.property

/-- 固定した同じ有限点 x の作用差分は、元の有限捩れ加法群への群準同型。 -/
def inertiaDifferenceCharacter (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative (Torsion S.rationalCurve (p ^ (n + 1))) :=
  UnipotentDifferenceCharacter.character irep
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) x

/-- 同じ差分準同型の値はすべて、同じ全慣性群に固定される。 -/
theorem inertiaDifferenceCharacter_fixed (σ τ : inertiaSubgroupIn A ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    irep σ (Multiplicative.toAdd (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x τ)) =
      Multiplicative.toAdd (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x τ) :=
  UnipotentDifferenceCharacter.difference_fixed irep
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) σ τ x
end Local

section Stage
variable {S}
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ上位有限捩れ商への実際の差分準同型。 -/
def ResidualCyclicStage.inertiaQuotientDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative T.upperQuotient :=
  (QuotientAddGroup.mk' T.upperStage).toMultiplicative.comp
    (S.inertiaDifferenceCharacter (n + 1) hp5 hq hqp haddr A hA x)

/-- 値は元の同じ点作用差の商類。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (τ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) =
      (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve (p ^ (n + 1 + 1)) τ.val x - x) := rfl

/-- 商値準同型の全ての値は、同じ商作用の全慣性元に固定される。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ τ : inertiaSubgroupIn A ℚ) :
    T.upperQuotientAction σ.val
      (Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ)) =
      Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) := by
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x τ]
  apply T.upperClass_fixed
  exact congrArg Subtype.val (S.inertiaDifferenceCharacter_fixed (n + 1) hp5 hq hqp haddr A hA σ τ x)
end Stage

variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ狭い失敗点を基点とすると、同じ慣性元で非自明かつ厳密位数 p の商値を持つ。 -/
theorem NarrowAbsorptionObstruction.inertia_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  have ho := T.upperClass_order_eq_prime
    (representation S.rationalCurve (p ^ (n + 1 + 1)) τ x - x) h.escapes h.difference_p_mem
  constructor
  · intro he
    have hz := congrArg Multiplicative.toAdd he
    exact h.escapes ((QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mp hz)
  · exact ho

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
/-- hclass と同じ Cofixed 候補から、通常の非自明な慣性商値準同型を内部構成する。 -/
theorem residual_exists_nontrivial_inertia_quotient_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.inertia_character_nontrivial hp5⟩

end
end DkMath.FLT.Frey.Source
