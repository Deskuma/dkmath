/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedTameCharacter
import DkMath.Lib.RepresentationTheory.TrivialCharacterH1

#print "file: DkMath.FLT.FreyFixedInertiaH1"

/-!
# 同じ慣性固定係数の通常の H¹ と非零性

F=Q^I には自明作用を入れる。通常の H¹ と、代表指標の連続性を別々に証明する。
Mathlib の連続群コホモロジーへの比較・同一視は行わない。
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

/-- 同じ固定部分群 F を自明作用の係数とする、馴分岐商の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedTameH1Class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1 (TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A)) :=
  TrivialCharacterH1.cohomologyClass (T.fixedTameCharacter hp5 hq hqp haddr A hA x)

/-- 同じ固定部分群値の慣性指標が与える、慣性群の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedInertiaH1Class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1 (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)) :=
  TrivialCharacterH1.cohomologyClass (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)

/-- 同じ代表 cocycle は、元の慣性群から馴分岐商へ写した同じ元で一致する。 -/
theorem ResidualCyclicStage.fixedCocycle_inflation_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ =
      TrivialCharacterH1.cocycle (T.fixedTameCharacter hp5 hq hqp haddr A hA x) (QuotientGroup.mk σ) := rfl

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害値は、固定部分群へ制限しても非自明。 -/
theorem NarrowAbsorptionObstruction.fixed_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      ⟨τ, h.inertia⟩ ≠ 1 := by
  dsimp only
  intro he
  have h' := congrArg (fun z : Multiplicative (T.inertiaFixedUpperQuotient A) =>
    Multiplicative.ofAdd (Multiplicative.toAdd z).val) he
  exact (h.inertia_character_nontrivial hp5).1 h'

/-- 同じ証人で、自明作用の固定係数における二つの通常の H¹ 類は非零。 -/
theorem NarrowAbsorptionObstruction.fixed_H1_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 := by
  constructor
  · apply TrivialCharacterH1.class_ne_zero
    exact ⟨QuotientGroup.mk ⟨τ, h.inertia⟩, h.fixed_character_nontrivial hp5⟩
  · apply TrivialCharacterH1.class_ne_zero
    exact ⟨⟨τ, h.inertia⟩, h.fixed_character_nontrivial hp5⟩

end
end DkMath.FLT.Frey.Source
