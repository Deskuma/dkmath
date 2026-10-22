/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticReductionKernel
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.EllipticGoodReductionKernel"

/-!
# NOTE-031-004B: 良還元の全点で慣性変化量は実際の還元核に入る

整座標の場合、慣性は剰余座標を固定する。良還元の滑らかさと既存の割線・接線評価から
差点は無限遠か極となる。非整座標の場合、慣性は付値環への所属を保存するため
元の点も移された点も還元核に入り、既に証明した部分群の差の閉性を使える。
位数の単元性を一切使わないので、E[p]をp上で調べる際にも適用できる。
-/
namespace DkMath.Lib.NumberTheory.EllipticGoodReductionKernel
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticDyadicSeparation EllipticReductionKernel EllipticTorsionRepresentation
open ValuationInertia ValuationTameCharacter.TameCharacter

/-- 同じ剰余座標を持つ良還元の有限整点の差は実際の還元核に属する。 -/
theorem difference_mem_of_congruence {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (V : WeierstrassCurve K) (hV : Integral A V)
    (hgood : (hV.model.map (IsLocalRing.residue A)).Δ ≠ 0)
    {x₁ y₁ x₂ y₂ : K} (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hxx : x₁ - x₂ ∈ A.nonunits) (hyy : y₁ - y₂ ∈ A.nonunits) :
    Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ ∈ ofIntegral A V hV := by
  rw [mem_ofIntegral_iff]
  by_cases he : x₁ = x₂ ∧ y₁ = y₂
  · obtain ⟨rfl, rfl⟩ := he
    simpa only [sub_self] using (poleOrZero_zero (A := A) (W := V))
  · have hneg := (nonsingular_neg ..).mpr h₂
    have hne : ¬ (x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ (V.toAffine.negY x₂ y₂)) := by
      rwa [negY_negY]
    rw [sub_eq_add_neg, Point.neg_some, Point.add_some hne, poleOrZero_some_iff]
    have hs : EllipticGoodReductionSeparation.SmoothCoordinates hV.model x₁ y₁ :=
      EllipticGoodReductionSeparation.hasSmoothReduction_of_good hV.model hgood
        (Point.some x₁ y₁ h₁) x₁ y₁ h₁ rfl
    have ha := EllipticGoodReductionSeparation.addX_notMem_of_sub_mem_nonunits_of_smooth
      hV.model hs h₁.1 hneg.1 hx₁ hx₂ hne hxx (by
        change y₁ - V.toAffine.negY x₂ (V.toAffine.negY x₂ y₂) ∈ A.nonunits
        simpa only [negY_negY] using hyy)
    exact lt_of_not_ge (fun h => ha ((A.valuation_le_one_iff _).mp h))

/-- 良還元では、全ての実点の慣性変化量が同じ還元核へ吸収される。
捩れ位数が剰余標数と一致する場合を排除しない。 -/
theorem inertia_difference_mem (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hV : Integral A (E.baseChange (AlgebraicClosure ℚ)))
    (hgood : (hV.model.map (IsLocalRing.residue A)).Δ ≠ 0)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : Points E) : pointAction E σ P - P ∈ ofIntegral A (E.baseChange (AlgebraicClosure ℚ)) hV := by
  classical
  let V := E.baseChange (AlgebraicClosure ℚ)
  let H := ofIntegral A V hV
  cases P with
  | zero => exact H.zero_mem
  | some x y h =>
    change Point.map σ.toAlgHom (Point.some x y h) - Point.some x y h ∈ H
    rw [Point.map_some]
    by_cases hx : x ∈ A
    · have hdec := (mem_inertiaSubgroupIn_iff.mp hσ).1
      exact difference_mem_of_congruence A V hV hgood _ h ((apply_mem_iff hdec x).mpr hx) hx
        (ValuationPrimeSupport.inertia_apply_sub_mem_nonunits A ℚ σ hσ hx)
        (ValuationPrimeSupport.inertia_apply_sub_mem_nonunits A ℚ σ hσ
          ((A.valuation_le_one_iff _).mp (v_y_le_one hV h.1 ((A.valuation_le_one_iff _).mpr hx))))
    · apply H.sub_mem
      · rw [mem_ofIntegral_iff, poleOrZero_some_iff]
        exact lt_of_not_ge (fun hv => hx ((apply_mem_iff (mem_inertiaSubgroupIn_iff.mp hσ).1 x).mp
          ((A.valuation_le_one_iff _).mp hv)))
      · rw [mem_ofIntegral_iff, poleOrZero_some_iff]
        exact lt_of_not_ge (fun hv => hx ((A.valuation_le_one_iff _).mp hv))

end DkMath.Lib.NumberTheory.EllipticGoodReductionKernel
