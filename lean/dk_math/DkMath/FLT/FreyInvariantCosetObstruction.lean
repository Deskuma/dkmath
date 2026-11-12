/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedCoefficientSequence

#print "file: DkMath.FLT.FreyInvariantCosetObstruction"

/-!
# 同じ Q/F の不変剰余類と不変な持ち上げの障害

作用差が F に入るため [x]+F は不変。障害点では非零で、不変な Q の元へ持ち上がらない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 元の同じ [x] を Q/F へ写すと、同じ実際の商作用で不変になる。 -/
def ResidualCyclicStage.fixedCosetInvariant
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.fixedQuotientCoefficient A).ρ.invariants :=
  ⟨T.fixedCoefficientProjection A ((QuotientAddGroup.mk' T.upperStage) x), by
    intro σ
    change (T.fixedCoefficientSubmodule A).mkQ
        (T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)
    have hm : T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
        (QuotientAddGroup.mk' T.upperStage) x ∈ T.fixedCoefficientSubmodule A := by
      have hf := (Multiplicative.toAdd
        (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ)).property
      exact (T.inertiaQuotientDifferenceCharacter_coboundary hp5 hq hqp haddr A hA x σ) ▸ hf
    apply sub_eq_zero.mp
    exact (map_sub (T.fixedCoefficientSubmodule A).mkQ _ _).symm.trans
      ((Submodule.Quotient.mk_eq_zero _).mpr hm)⟩

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害証明書の不変剰余類は非零。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_ne_zero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val ≠ 0 := by
  dsimp only
  intro hz
  have hx : (QuotientAddGroup.mk' T.upperStage) (⟨y, h.killed⟩ : Torsion S.rationalCurve (p ^ (n + 1 + 1))) ∈
      T.fixedCoefficientSubmodule A := (Submodule.Quotient.mk_eq_zero _).mp hz
  apply (h.inertia_character_nontrivial hp5).1
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩) = 0
  rw [T.inertiaQuotientDifferenceCharacter_coboundary hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩, hx τ h.inertia, sub_self]

/-- この同じ剰余類は、元の Q の不変元による持ち上げを持たない。 -/
theorem NarrowAbsorptionObstruction.no_invariant_lift
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    ¬ ∃ z : (T.fullInertiaCoefficient A).ρ.invariants,
      T.fixedCoefficientProjection A z.val =
        (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val := by
  dsimp only
  rintro ⟨z, hz⟩
  have hz0 : T.fixedCoefficientProjection A z.val = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro σ hσ
    exact z.property ⟨σ, hσ⟩
  exact h.fixedCoset_ne_zero hp5 (hz.symm.trans hz0)

end
end DkMath.FLT.Frey.Source
