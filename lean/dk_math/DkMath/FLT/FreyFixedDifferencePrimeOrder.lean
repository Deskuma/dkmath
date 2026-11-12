/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelCertificate

#print "file: DkMath.FLT.FreyFixedDifferencePrimeOrder"

/-!
# 同じ固定差分の厳密位数と固定部分群の素数因子

元の障害点 y と慣性元 τ を保持する。核の非零性とは別に、固定係数 F 自体にも
位数 p の元がある。F 全体が巡回であるとは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ慣性元で評価した、F に属する同じ差分。 -/
def NarrowAbsorptionObstruction.fixedDifference
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.inertiaFixedUpperQuotient A :=
  Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩)

/-- 値域制限後も、同じ固定差分の厳密位数は p。 -/
theorem NarrowAbsorptionObstruction.fixedDifference_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    addOrderOf (h.fixedDifference hp5) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · exact h.fixed_character_values_killed hp5 ⟨τ, h.inertia⟩
  · intro hz
    have he := congrArg (fun v : T.inertiaFixedUpperQuotient A => Multiplicative.ofAdd v.val) hz
    exact (h.inertia_character_nontrivial hp5).1 he

/-- F の中の同じ差分が生成する巡回部分群は濃度 p。 -/
theorem NarrowAbsorptionObstruction.fixedDifference_cyclic_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    Nat.card (AddSubgroup.zmultiples (h.fixedDifference hp5)) = p :=
  (Nat.card_zmultiples _).trans (h.fixedDifference_order_eq_prime hp5)

/-- Lagrange により、固定部分群 F 全体の濃度は p で割れる。 -/
theorem NarrowAbsorptionObstruction.prime_dvd_fixed_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    p ∣ Nat.card (T.inertiaFixedUpperQuotient A) := by
  have hd := (AddSubgroup.zmultiples (h.fixedDifference hp5)).card_addSubgroup_dvd_card
  exact dvd_trans ((h.fixedDifference_cyclic_card hp5).symm ▸ dvd_refl p) hd

end
end DkMath.FLT.Frey.Source
