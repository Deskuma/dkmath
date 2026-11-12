/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageLocalComponent
import DkMath.Lib.Algebra.CyclicIntersectionGenerator

#print "file: DkMath.FLT.FreyStageIntersectionGenerator"

/-!
# 同じ交叉指数を実際の生成元・倍点・厳密位数へ戻す

滑らかな部分群での局所商を保持する。判別式や Néron 成分群の次数公式は含まない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open EllipticGoodReductionSeparation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ局所商における実際の座標生成元の厳密位数。 -/
theorem ResidualCyclicStage.local_generator_order (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) =
      Nat.card (T.localComponentImage A) :=
  CyclicIntersectionGenerator.quotient_generator_order T.carrier (S.valuationSmoothSubgroup A) T.coordinates

/-- 交叉指数 r が与えられたとき、元の同じ交叉の実際の生成倍点。 -/
theorem ResidualCyclicStage.smooth_intersection_generator (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ} (hr : r ≤ n + 1)
    (hI : Nat.card (T.smoothIntersection A) = p ^ r) :
    T.smoothIntersection A = AddSubgroup.zmultiples (p ^ (n + 1 - r) • (T.coordinates 1).val) :=
  CyclicIntersectionGenerator.intersection_eq_zmultiples T.carrier (S.valuationSmoothSubgroup A)
    T.coordinates T.card hr hI

/-- 同じ生成元の k 倍が滑らかになる条件を、厳密位数による整数可除性で判定する。 -/
theorem ResidualCyclicStage.generator_multiple_smooth_iff (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (k : ℕ) :
    HasSmoothReduction (S.valuationModel A) (k • (T.coordinates 1).val) ↔
      Nat.card (T.localComponentImage A) ∣ k := by
  rw [← S.mem_valuationSmoothSubgroup_iff]
  calc
    k • (T.coordinates 1).val ∈ S.valuationSmoothSubgroup A ↔
        (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (k • (T.coordinates 1).val) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).symm
    _ ↔ k • (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val = 0 := by rw [map_nsmul]
    _ ↔ addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) ∣ k :=
      addOrderOf_dvd_iff_nsmul_eq_zero.symm
    _ ↔ _ := by rw [T.local_generator_order A]

/-- 非滑らかな同じ生成元について、最初に滑らかになる p 冪指数まで確定する。 -/
theorem ResidualCyclicStage.local_generator_profile_of_not_smooth (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hg : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) = p ^ (n + 1 - r) ∧
      T.smoothIntersection A = AddSubgroup.zmultiples (p ^ (n + 1 - r) • (T.coordinates 1).val) ∧
      ∀ k : ℕ, HasSmoothReduction (S.valuationModel A) (p ^ k • (T.coordinates 1).val) ↔ n + 1 - r ≤ k := by
  obtain ⟨r, hr, hI, hQ, _⟩ := T.local_component_profile_of_not_smooth A hg
  refine ⟨r, hr, hI, (T.local_generator_order A).trans hQ,
    T.smooth_intersection_generator A (by omega) hI, ?_⟩
  intro k
  rw [T.generator_multiple_smooth_iff A, hQ, Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt]

end
end DkMath.FLT.Frey.Source
