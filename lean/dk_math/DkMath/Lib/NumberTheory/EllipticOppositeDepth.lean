/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_level_add_of_branch_ne_of_level_lt,
blob 8bf0c52bab9d664cd941063ad7f43e9d7e0a0416.
Modified: arbitrary field and same DkMath C; reuse shallow quadratic estimate and translated equation.
-/

import DkMath.Lib.NumberTheory.EllipticAdditionDepth

#print "file: DkMath.Lib.NumberTheory.EllipticOppositeDepth"

/-!
# NOTE-031-002: 異なる枝・異なる深さの加法

v(X₁)<v(X₂)で両点が浅く異なる枝なら、和の深さNはN·v(X₂)=v(X₁)を満たす。
和の枝は第一点の枝を保つ。非零のX差と実際の有限和を先に構成し、
中心傾きの二次式の小ささは既存の同じCから供給する。
-/
namespace DkMath.Lib.NumberTheory.EllipticOppositeDepth
open WeierstrassCurve Affine Affine.Point EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticAdditionDepth
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve K}
private theorem cancel_lt {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b c : Γ}
    (h : a * c < b * c) : a < b := by
  by_contra hn
  exact (not_lt_of_ge (mul_le_mul' (not_lt.mp hn) le_rfl)) h
private theorem pos_of_nonzero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    (h : a ≠ 0) : 0 < a := zero_lt_iff.mpr h

/-- 異なる枝で第一点のX付値が小さい場合、同じ点群の和を構成し、正確な深さと枝を返す。
第二点の浅さは、第一点の浅さと深さの厳密な順序から導く。 -/
theorem opposite_branch_add_of_depth_lt [DecidableEq K] (C : CriticalCentre A W)
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hX₂ : A.valuation (x₂ - C.x) < 1) (hlt : A.valuation (x₁ - C.x) < A.valuation (x₂ - C.x))
    (hsh₁ : A.valuation (equationDefect W C.x C.y)
      < A.valuation (x₁ - C.x) ^ 2)
    (hbr : A.valuation ((y₁ - C.y) / (x₁ - C.x) - (y₂ - C.y) / (x₂ - C.x)) = 1) :
    ∃ (x₃ y₃ : K)
      (h₃ : W.toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      A.valuation (x₃ - C.x) * A.valuation (x₂ - C.x) = A.valuation (x₁ - C.x) ∧
      A.valuation ((y₃ - C.y) / (x₃ - C.x) - (y₁ - C.y) / (x₁ - C.x)) < 1 := by
  classical
  have hFy := C.derivativeY
  have ca₁ : W.toAffine.a₁ = W.a₁ := rfl
  have ca₂ : W.toAffine.a₂ = W.a₂ := rfl
  have ca₃ : W.toAffine.a₃ = W.a₃ := rfl
  have S₁ := translated_point C h₁.1
  have S₂ := translated_point C h₂.1
  obtain ⟨vF, hvF⟩ : ∃ g, A.valuation (equationDefect W C.x C.y) = g := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ g, A.valuation (x₁ - C.x) = g := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ g, A.valuation (x₂ - C.x) = g := ⟨_, rfl⟩
  rw [hvF, hv₁] at hsh₁
  rw [hv₁, hv₂] at hlt
  rw [hv₂] at hX₂
  have hX₁0 : x₁ - C.x ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hv₁
    rw [← hv₁, zero_pow two_ne_zero] at hsh₁
    exact absurd hsh₁ (not_lt.mpr zero_le)
  have hv₁0 : 0 < v₁ := hv₁ ▸ pos_of_nonzero ((Valuation.ne_zero_iff _).mpr hX₁0)
  have hv₂0 : 0 < v₂ := lt_trans hv₁0 hlt
  have hX₂0 : x₂ - C.x ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hv₂; rw [← hv₂] at hv₂0; exact lt_irrefl _ hv₂0
  have hx12 : x₁ ≠ x₂ := by
    intro h12; rw [h12, hv₂] at hv₁; rw [hv₁] at hlt; exact lt_irrefl _ hlt
  have hX12 : (x₁ - C.x) - (x₂ - C.x) ≠ 0 := by
    rw [sub_sub_sub_cancel_right]; exact sub_ne_zero.mpr hx12
  have hsh₂ : vF < v₂ ^ 2 := lt_trans hsh₁ (pow_lt_pow_left₀ hlt zero_le two_ne_zero)
  have hvX12 : A.valuation ((x₁ - C.x) - (x₂ - C.x)) = v₂ := by
    have hlt' : A.valuation (x₁ - C.x) < A.valuation (-(x₂ - C.x)) := by rw [Valuation.map_neg, hv₁, hv₂]; exact hlt
    have := Valuation.map_add_eq_of_lt_left _ hlt'
    rw [show -(x₂ - C.x) + (x₁ - C.x) = (x₁ - C.x) - (x₂ - C.x) by ring] at this
    rw [this, Valuation.map_neg, hv₂]
  have hshR₁ : A.valuation (equationDefect W C.x C.y) < A.valuation (x₁ - C.x) ^ 2 := by
    rw [hvF, hv₁]; exact hsh₁
  have hshR₂ : A.valuation (equationDefect W C.x C.y) < A.valuation (x₂ - C.x) ^ 2 := by
    rw [hvF, hv₂]; exact hsh₂
  have hq₁ := quadratic_small_of_shallow C h₁.1 (hv₁ ▸ hlt.trans hX₂) hshR₁
  have hq₂ := quadratic_small_of_shallow C h₂.1 (hv₂ ▸ hX₂) hshR₂
  have hsumt : A.valuation ((y₁ - C.y) / (x₁ - C.x) + (y₂ - C.y) / (x₂ - C.x) + W.a₁) < 1 := by
    have hprod : A.valuation (((y₁ - C.y) / (x₁ - C.x) - (y₂ - C.y) / (x₂ - C.x))
        * ((y₁ - C.y) / (x₁ - C.x) + (y₂ - C.y) / (x₂ - C.x) + W.a₁)) < 1 := by
      have := Valuation.map_sub_lt _ hq₁ hq₂
      dsimp only [centreSlope] at this
      convert this using 2
      ring
    rwa [map_mul, hbr, one_mul] at hprod
  refine ⟨_, _, _, Point.add_of_X_ne hx12, ?_⟩
  rw [slope_of_X_ne hx12]
  obtain ⟨l, hl⟩ : ∃ l, (y₁ - y₂) / (x₁ - x₂) = l := ⟨_, rfl⟩
  rw [hl]
  have hL : l * ((x₁ - C.x) - (x₂ - C.x)) = (y₁ - C.y) - (y₂ - C.y) := by
    rw [← hl, sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
    field_simp [sub_ne_zero.mpr hx12]
  have hX3 : W.toAffine.addX x₁ x₂ l - C.x
      = l ^ 2 + W.a₁ * l - (W.a₂ + 3 * C.x)
        - (x₁ - C.x) - (x₂ - C.x) := by
    rw [WeierstrassCurve.Affine.addX, ca₁, ca₂]; ring
  have hY3 : W.toAffine.addY x₁ x₂ y₁ l - C.y
      = -(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - C.x)
        - ((y₁ - C.y) - l * (x₁ - C.x)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, ca₁, ca₃]
    linear_combination -hFy
  obtain ⟨X₃, hX₃def⟩ : ∃ X, W.toAffine.addX x₁ x₂ l - C.x = X :=
    ⟨_, rfl⟩
  rw [hX₃def] at hX3 hY3
  have hx₃ : W.toAffine.addX x₁ x₂ l = X₃ + C.x := by
    rw [← hX₃def]; ring
  have hy₃ : W.toAffine.addY x₁ x₂ y₁ l
      = -(l + W.a₁) * X₃ - ((y₁ - C.y) - l * (x₁ - C.x)) + C.y := by
    rw [← hY3]; ring
  rw [hx₃, hy₃, add_sub_cancel_right, add_sub_cancel_right]
  have F1 : (x₁ - C.x) * (x₂ - C.x) * X₃ = ((y₁ - C.y) - l * (x₁ - C.x)) ^ 2
      + (equationDefect W C.x C.y) := by
    have hmul : ((x₁ - C.x) - (x₂ - C.x)) * ((x₁ - C.x) * (x₂ - C.x) * X₃ - ((y₁ - C.y) - l * (x₁ - C.x)) ^ 2
        - (equationDefect W C.x C.y)) = 0 := by
      rw [hX3]
      linear_combination (x₂ - C.x) * S₁ - (x₁ - C.x) * S₂
        + (x₁ - C.x) * (-(x₁ - C.x) * l + (x₂ - C.x) * W.a₁ + (x₂ - C.x) * l + (y₁ - C.y) + (y₂ - C.y)) * hL
    have := (mul_eq_zero.mp hmul).resolve_left hX12
    linear_combination this
  have hD : (x₂ - C.x) * (y₁ - C.y) - (x₁ - C.x) * (y₂ - C.y)
      = (x₁ - C.x) * (x₂ - C.x) * ((y₁ - C.y) / (x₁ - C.x) - (y₂ - C.y) / (x₂ - C.x)) := by
    field_simp
  have hvD : A.valuation ((x₂ - C.x) * (y₁ - C.y) - (x₁ - C.x) * (y₂ - C.y)) = v₁ * v₂ := by
    rw [hD, map_mul, map_mul, hbr, hv₁, hv₂, mul_one]
  have F2 : ((y₁ - C.y) - l * (x₁ - C.x)) * ((x₁ - C.x) - (x₂ - C.x))
      = -((x₂ - C.x) * (y₁ - C.y) - (x₁ - C.x) * (y₂ - C.y)) := by
    linear_combination -(x₁ - C.x) * hL
  have hvν : A.valuation ((y₁ - C.y) - l * (x₁ - C.x)) = v₁ := by
    have := congrArg A.valuation F2
    rw [map_mul, Valuation.map_neg, hvD, hvX12] at this
    exact mul_right_cancel₀ (ne_of_gt hv₂0) this
  have hvν2 : A.valuation (((y₁ - C.y) - l * (x₁ - C.x)) ^ 2
      + (equationDefect W C.x C.y)) = v₁ ^ 2 := by
    have hlt' : A.valuation (equationDefect W C.x C.y)
        < A.valuation (((y₁ - C.y) - l * (x₁ - C.x)) ^ 2) := by
      rw [map_pow, hvν, hvF]; exact hsh₁
    rw [Valuation.map_add_eq_of_lt_left _ hlt', map_pow, hvν]
  have hvX₃ : A.valuation X₃ * v₂ = v₁ := by
    have := congrArg A.valuation F1
    rw [map_mul, map_mul, hv₁, hv₂, hvν2, sq] at this
    have := mul_left_cancel₀ (ne_of_gt hv₁0) ((mul_assoc v₁ v₂ _).symm.trans this |>.symm).symm
    rw [mul_comm] at this
    exact this
  have hX₃0 : X₃ ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero, zero_mul] at hvX₃
    exact absurd hvX₃ (ne_of_lt hv₁0)
  have hvX₃0 : 0 < A.valuation X₃ := pos_of_nonzero ((Valuation.ne_zero_iff _).mpr hX₃0)
  refine ⟨by rw [hv₁, hv₂]; exact hvX₃, ?_⟩
  have F4 : (l - (y₂ - C.y) / (x₂ - C.x)) * ((x₂ - C.x) * ((x₁ - C.x) - (x₂ - C.x)))
      = (x₂ - C.x) * (y₁ - C.y) - (x₁ - C.x) * (y₂ - C.y) := by
    have : (l - (y₂ - C.y) / (x₂ - C.x)) * (x₂ - C.x) = l * (x₂ - C.x) - (y₂ - C.y) := by
      field_simp
    calc (l - (y₂ - C.y) / (x₂ - C.x)) * ((x₂ - C.x) * ((x₁ - C.x) - (x₂ - C.x)))
        = ((l - (y₂ - C.y) / (x₂ - C.x)) * (x₂ - C.x)) * ((x₁ - C.x) - (x₂ - C.x)) := by ring
      _ = (l * (x₂ - C.x) - (y₂ - C.y)) * ((x₁ - C.x) - (x₂ - C.x)) := by rw [this]
      _ = (x₂ - C.x) * (y₁ - C.y) - (x₁ - C.x) * (y₂ - C.y) := by linear_combination (x₂ - C.x) * hL
  have hvlt₂ : A.valuation (l - (y₂ - C.y) / (x₂ - C.x)) < 1 := by
    have := congrArg A.valuation F4
    rw [map_mul, map_mul, hvX12, hv₂, hvD] at this
    have h1 : A.valuation (l - (y₂ - C.y) / (x₂ - C.x)) * v₂ = v₁ := by
      apply mul_right_cancel₀ (ne_of_gt hv₂0)
      rw [mul_assoc]; exact this
    have h2 : A.valuation (l - (y₂ - C.y) / (x₂ - C.x)) * v₂ < 1 * v₂ := by rw [h1, one_mul]; exact hlt
    exact cancel_lt h2
  have hvνX₃ : A.valuation (((y₁ - C.y) - l * (x₁ - C.x)) / X₃) < 1 := by
    have h1 : A.valuation (((y₁ - C.y) - l * (x₁ - C.x)) / X₃) * A.valuation X₃ = v₁ := by
      rw [← map_mul, div_mul_cancel₀ _ hX₃0, hvν]
    have h2 : A.valuation (((y₁ - C.y) - l * (x₁ - C.x)) / X₃) * A.valuation X₃ = v₂ * A.valuation X₃ := by
      rw [h1, mul_comm, hvX₃]
    have h3 := mul_right_cancel₀ (ne_of_gt hvX₃0) h2
    rw [h3]; exact hX₂
  have ht3 : (-(l + W.a₁) * X₃ - ((y₁ - C.y) - l * (x₁ - C.x))) / X₃ - (y₁ - C.y) / (x₁ - C.x)
      = -((l - (y₂ - C.y) / (x₂ - C.x)) + ((y₁ - C.y) / (x₁ - C.x) + (y₂ - C.y) / (x₂ - C.x) + W.a₁)
          + ((y₁ - C.y) - l * (x₁ - C.x)) / X₃) := by
    field_simp
    ring
  rw [ht3, Valuation.map_neg]
  exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hvlt₂ hsumt) hvνX₃

end DkMath.Lib.NumberTheory.EllipticOppositeDepth
