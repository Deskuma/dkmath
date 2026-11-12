/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySmoothStageAbsorption
import DkMath.Lib.Algebra.FiniteSubgroupIntersection

#print "file: DkMath.FLT.FreyStageLocalComponent"

/-!
# 同じ巡回段の滑らかな交叉と局所商像

局所商は元の実際の点群を既存の滑らかな部分群で割った商。
Néron 成分群との同定や判別式による成分群次数の公式を仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open EllipticGoodReductionSeparation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 元の同じ段と同じ滑らかな部分群の交叉。 -/
def ResidualCyclicStage.smoothIntersection (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) : AddSubgroup (Points S.rationalCurve) :=
  T.carrier ⊓ S.valuationSmoothSubgroup A

/-- 元の段の、同じ局所点群商における実際の像。 -/
def ResidualCyclicStage.localComponentImage (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (Points S.rationalCurve ⧸ S.valuationSmoothSubgroup A) :=
  T.carrier.map (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A))

/-- 同じ二つの濃度を相補的な p 冪指数で正確に記述する。 -/
theorem ResidualCyclicStage.local_component_profile (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ r ≤ n + 1, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) :=
  FiniteSubgroupIntersection.prime_power_profile T.carrier (S.valuationSmoothSubgroup A)
    (Fact.out : p.Prime) T.card

/-- 生成元が非滑らかなら、交叉は真に小さく、局所商像は少なくとも p 元を持つ。 -/
theorem ResidualCyclicStage.local_component_profile_of_not_smooth (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hg : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
      p ≤ Nat.card (T.localComponentImage A) := by
  obtain ⟨r, hr, hI, hQ⟩ := T.local_component_profile A
  have hlt : r < n + 1 := by
    by_contra h
    have he : r = n + 1 := by omega
    let := T.finite
    have hc : Nat.card ↥(T.carrier ⊓ S.valuationSmoothSubgroup A) = Nat.card T.carrier := by
      simpa only [smoothIntersection, he, T.card] using hI
    have hEq : T.carrier ⊓ S.valuationSmoothSubgroup A = T.carrier :=
      AddSubgroup.eq_of_le_of_card_ge inf_le_left hc.ge
    have hmem : (T.coordinates 1).val ∈ T.carrier ⊓ S.valuationSmoothSubgroup A :=
      hEq.symm ▸ (T.coordinates 1).property
    exact hg ((S.mem_valuationSmoothSubgroup_iff A _).mp hmem.2)
  refine ⟨r, by omega, hI, hQ, ?_⟩
  rw [hQ]
  calc
    p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (n + 1 - r) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)

end
end DkMath.FLT.Frey.Source
