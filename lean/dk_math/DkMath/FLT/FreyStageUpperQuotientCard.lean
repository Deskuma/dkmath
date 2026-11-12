/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageUpperQuotient
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.FLT.FreyStageUpperQuotientCard"

/-!
# 元の同じ段による一段上の捩れ商の正確な濃度

E[p^(n+2)]/T の濃度は p^(n+3)。元の点と段を保つ加法同型で計算する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 上位捩れ内の段と元の同じ T は、同じ点を保つ加法同型。 -/
def ResidualCyclicStage.upperStageEquiv (T : S.ResidualCyclicStage L n) :
    T.upperStage ≃+ T.carrier where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by
    change p ^ (n + 1 + 1) • x.val = 0
    rw [pow_succ, mul_nsmul, T.killed x.val x.property, nsmul_zero]⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 元の段の濃度をそのまま保持する。 -/
theorem ResidualCyclicStage.upperStage_card (T : S.ResidualCyclicStage L n) :
    Nat.card T.upperStage = p ^ (n + 1) :=
  (Nat.card_congr T.upperStageEquiv.toEquiv).trans T.card

/-- 実際の一段上の有限捩れ商の濃度は正確に p^(n+3)。 -/
theorem ResidualCyclicStage.upperQuotient_card (T : S.ResidualCyclicStage L n) :
    Nat.card T.upperQuotient = p ^ (n + 3) := by
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  have hc := T.upperStage.card_eq_card_quotient_mul_card_addSubgroup
  rw [card_torsion_sq S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), T.upperStage_card] at hc
  apply mul_right_cancel₀ (pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero)
  calc
    Nat.card T.upperQuotient * p ^ (n + 1) = (p ^ (n + 1 + 1)) ^ 2 := hc.symm
    _ = p ^ (n + 3) * p ^ (n + 1) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end
end DkMath.FLT.Frey.Source
