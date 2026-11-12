/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTameResonance

#print "file: DkMath.FLT.FreyFixedTameCharacter"

/-!
# 同じ慣性固定係数への連続な馴分岐差分指標

元の Q の実際の固定部分群 F=Q^I に値を制限し、同じ野生部分群で割る。
係数 F と Q の違いを消さず、同じ値と証人を保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ固定部分群値の慣性指標は、元の部分群位相で連続。 -/
theorem ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_ofAdd.comp
  apply Continuous.subtype_mk
  exact continuous_toAdd.comp (T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x)

/-- 同じ野生部分群は、値域を実際の固定部分群へ制限しても核に入る。 -/
theorem ResidualCyclicStage.wildInertia_le_fixed_character_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    wildInertiaSubgroup A ≤ (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x).ker := by
  intro σ hσ
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd
    (T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x hσ)

/-- 同じ F=Q^I を値域とし、同じ実際の馴分岐商へ降ろした指標。 -/
def ResidualCyclicStage.fixedTameCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    tameInertiaQuotient A →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift (wildInertiaSubgroup A)
    (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)
    (T.wildInertia_le_fixed_character_kernel hp5 hq hqp haddr A hA x)

/-- 降下後も、同じ慣性元での同じ固定部分群値を保つ。 -/
theorem ResidualCyclicStage.fixedTameCharacter_mk
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.fixedTameCharacter hp5 hq hqp haddr A hA x (QuotientGroup.mk σ) =
      T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ := rfl

/-- 元の F→Q の包含で戻すと、以前と同じ馴分岐指標。 -/
theorem ResidualCyclicStage.fixedTameCharacter_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (t : tameInertiaQuotient A) :
    (Multiplicative.toAdd (T.fixedTameCharacter hp5 hq hqp haddr A hA x t)).val =
      Multiplicative.toAdd (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x t) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
  rfl

/-- 同じ標準商位相から、同じ離散固定部分群への連続性。 -/
theorem ResidualCyclicStage.fixedTameCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.fixedTameCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_quot_lift
  exact T.inertiaFixedDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

end
end DkMath.FLT.Frey.Source
