/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameFaithful

#print "file: DkMath.FLT.FreyCommonTamePGroup"

/-!
# 同じ共通有限商の p 群性・濃度・指数上界

忠実な値写像と元の F の濃度から計算する。巡回性は含めない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ H の濃度は、同じ F の |K| 個の積の濃度を割る。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_card_dvd :
    Nat.card (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) ∣
      Nat.card (T.inertiaFixedUpperQuotient A) ^ Nat.card (T.fixedH1CoefficientKernel A) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  have hd := Subgroup.card_dvd_of_injective (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA)
    (T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA)
  simpa only [Nat.card_fun, Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (T.inertiaFixedUpperQuotient A) ≃ T.inertiaFixedUpperQuotient A)] using hd

/-- 同じ共通商の各元は、元の固定係数群 F の濃度乗で 1 になる。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    h ^ Nat.card (T.inertiaFixedUpperQuotient A) = 1 := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  rw [map_pow, map_one]
  apply funext
  intro k
  exact pow_card_eq_one'

/-- 元の F と同じ共通商 H の p 冪濃度を内部計算する。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile :
    ∃ r m, r ≤ n + 3 ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) = p ^ m := by
  have hdF : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm
  obtain ⟨r, hr, hF⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdF
  have hdH := T.fixedKernelCommonTame_card_dvd A hp5 hq hqp haddr hA
  rw [hF, ← pow_mul] at hdH
  obtain ⟨m, hm, hH⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdH
  exact ⟨r, m, hr, hm, hF, hH⟩

/-- 同じ実際の共通商は p 群である。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_isPGroup :
    IsPGroup p (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  obtain ⟨_, _, _, _, _, hH⟩ := T.fixedKernelCommonTame_prime_power_profile A hp5 hq hqp haddr hA
  exact IsPGroup.of_card hH

/-- 共通商の指数は、元の F の p 冪濃度で一様に抑えられる。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_exponent_profile :
    ∃ r ≤ n + 3, Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA, h ^ (p ^ r) = 1 := by
  obtain ⟨r, _, hr, _, hF, _⟩ := T.fixedKernelCommonTame_prime_power_profile A hp5 hq hqp haddr hA
  exact ⟨r, hr, hF, fun h => hF ▸ T.fixedKernelCommonTame_pow_card_fixed A hp5 hq hqp haddr hA h⟩

/-- 有限段生成元の消費に使う、段数だけで決まる一様な零化冪。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_pow_stage
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) : h ^ (p ^ (n + 3)) = 1 := by
  obtain ⟨r, hr, _, he⟩ := T.fixedKernelCommonTame_exponent_profile A hp5 hq hqp haddr hA
  exact orderOf_dvd_iff_pow_eq_one.mp
    (dvd_trans (orderOf_dvd_of_pow_eq_one (he h)) (pow_dvd_pow p hr))

end
end DkMath.FLT.Frey.Source
