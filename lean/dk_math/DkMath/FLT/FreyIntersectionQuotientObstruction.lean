/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction
import DkMath.FLT.FreyStageLocalComponent
import DkMath.FLT.FreyStageUpperQuotient

#print "file: DkMath.FLT.FreyIntersectionQuotientObstruction"

/-!
# 同じ障害の交叉・局所商像・有限捩れ商による記述

差点は局所滑らか商では零だが、元の段による有限商では厳密位数 p の慣性固定元。
類群消滅と Cofixed のもとで同じ証人を保って接続する。配置障害の排除は未証明。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ}
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の滑らかな交叉は p^r (r≤n)、局所商像は p^(n+1-r)≥p。 -/
theorem NarrowAbsorptionObstruction.intersection_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
      p ≤ Nat.card (T.localComponentImage A) :=
  T.local_component_profile_of_not_smooth A h.generator_not_smooth

/-- 同じ差点の局所滑らか商での像は零。有限捩れ商の非零元と取り違えない。 -/
theorem NarrowAbsorptionObstruction.difference_component_zero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (pointAction S.rationalCurve τ y - y) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr h.difference_smooth)

/-- 同じ差点は、一段上の有限捩れ商で厳密位数 p の全慣性固定元を与える。 -/
theorem NarrowAbsorptionObstruction.finite_quotient_witness
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
      x.val = pointAction S.rationalCurve τ y - y ∧
      addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p ∧
      ∀ σ ∈ inertiaSubgroupIn A ℚ,
        T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
          (QuotientAddGroup.mk' T.upperStage) x := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) :=
    ⟨pointAction S.rationalCurve τ y - y, h.difference_killed⟩
  refine ⟨x, rfl, T.upperClass_order_eq_prime x h.escapes h.difference_p_mem, ?_⟩
  intro σ hσ
  exact T.upperClass_fixed σ x (h.difference_fixed σ hσ)

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
/-- 同じ Cofixed 候補の障害を交叉濃度と厳密位数 p の商元で強化する。
新しい配置・吸収・商元の存在を provider として追加しない。 -/
theorem residual_exists_intersection_quotient_obstruction
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve),
      S.NarrowAbsorptionObstruction L T q A τ y ∧
      ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
        Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
        p ≤ Nat.card (T.localComponentImage A) ∧
        (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (pointAction S.rationalCurve τ y - y) = 0 ∧
      ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
        x.val = pointAction S.rationalCurve τ y - y ∧
        addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p ∧
        ∀ σ ∈ inertiaSubgroupIn A ℚ,
          T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
            (QuotientAddGroup.mk' T.upperStage) x := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  obtain ⟨r, hr, hI, hQ, hbound⟩ := h.intersection_profile
  exact ⟨n, T, q, A, τ, y, h, r, hr, hI, hQ, hbound, h.difference_component_zero, h.finite_quotient_witness⟩

end
end DkMath.FLT.Frey.Source
