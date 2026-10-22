/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_level_add_of_antipodal_of_shallow,
blob cbbcd3946ef7342ff6d114fd0b576355e4738dcc.
Modified: same existing DkMath C,D over arbitrary field; critical deviations reused independently
of root existence, and shallow branches supplied by DkMath classification.
-/

import DkMath.Lib.NumberTheory.EllipticOppositeDepth

#print "file: DkMath.Lib.NumberTheory.EllipticCriticalAddition"

/-!
# NOTE-031-002: 臨界側の点と浅い点の加法

v(X₁)²≤v(F₀)の点では、二方向の線形偏差の付値が等しく、その平方はv(F₀)となる。
浅い点を加えると和はその点と反対の枝へ移り、(N·v(X₂))²=v(F₀)を満たす。
中心と方向を取り直さず、実際の有限和とともに返す。
-/
namespace DkMath.Lib.NumberTheory.EllipticCriticalAddition
open WeierstrassCurve Affine Affine.Point EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticAdditionDepth
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve K}
local notation "v" => A.valuation
section Core
variable (W A)
private theorem critical_shallow_core [DecidableEq K] {x₀ y₀ F₀ α β : K}
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hsum : α + β = -W.a₁) (hprod : α * β = -(W.a₂ + 3 * x₀))
    (hαβ : v (α - β) = 1)
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hE₁ : (y₁ - y₀ - α * (x₁ - x₀)) * (y₁ - y₀ - β * (x₁ - x₀)) = (x₁ - x₀) ^ 3 - F₀)
    (hE₂ : (y₂ - y₀ - α * (x₂ - x₀)) * (y₂ - y₀ - β * (x₂ - x₀)) = (x₂ - x₀) ^ 3 - F₀)
    {u : A.ValueGroup} (hU₁ : v (y₁ - y₀ - α * (x₁ - x₀)) = u)
    (hV₁ : v (y₁ - y₀ - β * (x₁ - x₀)) = u) (huu : u * u = v F₀) (hu0 : 0 < u)
    (hf : v (x₁ - x₀) ≤ u)
    (hsh : v F₀ < v (x₂ - x₀) ^ 2) (hX₂ : v (x₂ - x₀) < 1)
    (hbr : v (y₂ - y₀ - α * (x₂ - x₀)) < v (x₂ - x₀)) :
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point)
          = Point.some x₃ y₃ h₃ ∧
        (v (x₃ - x₀) * v (x₂ - x₀)) ^ 2 = v F₀ ∧
        v ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1 := by
  set X₁ := x₁ - x₀ with hX₁def
  set X₂ := x₂ - x₀ with hX₂def
  set U₁ := y₁ - y₀ - α * (x₁ - x₀) with hU₁def
  set V₁ := y₁ - y₀ - β * (x₁ - x₀) with hV₁def
  set U₂ := y₂ - y₀ - α * (x₂ - x₀) with hU₂def
  set V₂ := y₂ - y₀ - β * (x₂ - x₀) with hV₂def
  set e := v X₂ with hedef
  have hu_lt_e : u < e := by
    apply (pow_lt_pow_iff_left₀ zero_le zero_le two_ne_zero).mp
    simpa only [sq, huu] using hsh
  have he0 : 0 < e := lt_trans hu0 hu_lt_e
  have he1 : e < 1 := hX₂
  have hf_lt_e : v X₁ < e := lt_of_le_of_lt hf hu_lt_e
  have hX₂0 : X₂ ≠ 0 := (Valuation.pos_iff _).mp he0
  have hx12 : x₁ ≠ x₂ := by
    intro h
    have : X₁ = X₂ := by rw [hX₁def, hX₂def, h]
    rw [this] at hf_lt_e
    exact lt_irrefl _ hf_lt_e
  have hX12 : X₁ - X₂ ≠ 0 := by
    rw [hX₁def, hX₂def]; intro h; apply hx12; linear_combination h
  have hvX12 : v (X₁ - X₂) = e := Valuation.map_sub_eq_of_lt_right _ hf_lt_e
  have hUV₂ : U₂ - V₂ = (β - α) * X₂ := by rw [hU₂def, hV₂def, hX₂def]; ring
  have hvβα : v (β - α) = 1 := by rw [← neg_sub, Valuation.map_neg]; exact hαβ
  have hvUV₂ : v (U₂ - V₂) = e := by rw [hUV₂, Valuation.map_mul, hvβα, one_mul, hedef]
  have hV₂ : v V₂ = e := by
    have h : V₂ = U₂ - (U₂ - V₂) := by ring
    have hlt : v U₂ < v (U₂ - V₂) := by rw [hvUV₂]; exact hbr
    rw [h, Valuation.map_sub_eq_of_lt_right _ hlt, hvUV₂]
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  have hℓeq : ℓ = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx12
  have hℓX : ℓ * (X₁ - X₂) = (y₁ - y₀) - (y₂ - y₀) := by
    have h : X₁ - X₂ = x₁ - x₂ := by rw [hX₁def, hX₂def]; ring
    rw [h, hℓeq, div_mul_cancel₀ _ (sub_ne_zero.mpr hx12)]; ring
  have hℓα : ℓ - α = (U₁ - U₂) / (X₁ - X₂) := by
    rw [eq_div_iff hX12, sub_mul, hℓX, hU₁def, hU₂def, hX₁def, hX₂def]; ring
  have hℓβ : ℓ - β = (V₁ - V₂) / (X₁ - X₂) := by
    rw [eq_div_iff hX12, sub_mul, hℓX, hV₁def, hV₂def, hX₁def, hX₂def]; ring
  have hvℓα : v (ℓ - α) < 1 := by
    rw [hℓα, map_div₀, hvX12, div_lt_one₀ he0]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hbr)
    rw [hU₁]; exact hu_lt_e
  have hvV12 : v (V₁ - V₂) = e := by
    rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hV₁, hV₂]; exact hu_lt_e), hV₂]
  have hvℓβ : v (ℓ - β) = 1 := by
    rw [hℓβ, map_div₀, hvX12, hvV12, div_self (ne_of_gt he0)]
  have hv2ℓ : v (2 * ℓ + W.a₁) = 1 := by
    have h : 2 * ℓ + W.a₁ = (ℓ - β) + (ℓ - α) := by linear_combination hsum
    rw [h, Valuation.map_add_eq_of_lt_left _ (by rw [hvℓβ]; exact hvℓα), hvℓβ]
  set ν := (y₁ - y₀) - ℓ * X₁ with hνdef
  have hνX : (X₁ - X₂) * ν = X₁ * U₂ - X₂ * U₁ := by
    rw [hνdef, hU₁def, hU₂def]
    linear_combination (-X₁) * hℓX
  have hvν : v ν = u := by
    have h1 : v (X₁ * U₂) < v (X₂ * U₁) := by
      rw [Valuation.map_mul, Valuation.map_mul, hU₁, ← hedef]
      calc v X₁ * v U₂ ≤ u * v U₂ := mul_le_mul' hf le_rfl
        _ < u * e := mul_lt_mul_of_pos_left hbr hu0
        _ = e * u := mul_comm _ _
    have h2 : v ((X₁ - X₂) * ν) = e * u := by
      rw [hνX, Valuation.map_sub_eq_of_lt_right _ h1, Valuation.map_mul, hU₁]
    rw [Valuation.map_mul, hvX12] at h2
    exact mul_left_cancel₀ (ne_of_gt he0) h2
  set X₃ := W.toAffine.addX x₁ x₂ ℓ - x₀ with hX₃def
  have hX₃V1 : X₃ = (ℓ - α) * (ℓ - β) - X₁ - X₂ := by
    rw [hX₃def, Affine.addX, hX₁def, hX₂def]
    linear_combination ℓ * hsum - hprod
  have hL₁ : (ℓ - α) * X₁ + ν = U₁ := by rw [hνdef, hU₁def, hX₁def]; ring
  have hL₁' : (ℓ - β) * X₁ + ν = V₁ := by rw [hνdef, hV₁def, hX₁def]; ring
  have hL₂ : (ℓ - α) * X₂ + ν = U₂ := by
    rw [hνdef, hU₂def, hX₂def]; linear_combination -hℓX
  have hL₂' : (ℓ - β) * X₂ + ν = V₂ := by
    rw [hνdef, hV₂def, hX₂def]; linear_combination -hℓX
  have hC₁ : ((ℓ - α) * X₁ + ν) * ((ℓ - β) * X₁ + ν) - X₁ ^ 3 + F₀ = 0 := by
    rw [hL₁, hL₁', hE₁]; ring
  have hC₂ : ((ℓ - α) * X₂ + ν) * ((ℓ - β) * X₂ + ν) - X₂ ^ 3 + F₀ = 0 := by
    rw [hL₂, hL₂', hE₂]; ring
  have hV2 : (X₁ + X₂) * X₃ = -(ν * (2 * ℓ + W.a₁)) - X₁ * X₂ := by
    have key : (X₁ - X₂) * ((X₁ + X₂) * X₃ + ν * (2 * ℓ + W.a₁) + X₁ * X₂) = 0 := by
      rw [hX₃V1]
      linear_combination hC₁ - hC₂ + ((X₁ - X₂) * ν) * hsum
    have := (mul_eq_zero.mp key).resolve_left hX12
    linear_combination this
  have hvX1X2 : v (X₁ + X₂) = e := Valuation.map_add_eq_of_lt_right _ hf_lt_e
  have hvRHS : v (-(ν * (2 * ℓ + W.a₁)) - X₁ * X₂) = u := by
    have h1 : v (-(ν * (2 * ℓ + W.a₁))) = u := by
      rw [Valuation.map_neg, Valuation.map_mul, hvν, hv2ℓ, mul_one]
    rw [Valuation.map_sub_eq_of_lt_left _ ?_, h1]
    rw [h1, Valuation.map_mul, ← hedef]
    calc v X₁ * e ≤ u * e := mul_le_mul' hf le_rfl
      _ < u * 1 := mul_lt_mul_of_pos_left he1 hu0
      _ = u := mul_one _
  have hvX₃ : v X₃ * e = u := by
    have h := congrArg (fun z => v z) hV2
    simp only [Valuation.map_mul, hvX1X2, hvRHS] at h
    rw [mul_comm] at h; exact h
  have hvX₃0 : 0 < v X₃ := by
    rcases eq_or_lt_of_le (zero_le (a := v X₃)) with h | h
    · rw [← h, zero_mul] at hvX₃; exact absurd hvX₃ (ne_of_lt hu0)
    · exact h
  have hX₃0 : X₃ ≠ 0 := (Valuation.pos_iff _).mp hvX₃0
  have hu_lt_X₃ : u < v X₃ := by
    calc u = v X₃ * e := hvX₃.symm
      _ < v X₃ * 1 := mul_lt_mul_of_pos_left he1 hvX₃0
      _ = v X₃ := mul_one _
  set Y₃ := W.toAffine.addY x₁ x₂ y₁ ℓ - y₀ with hY₃def
  have hY₃ : Y₃ = -(ℓ + W.a₁) * X₃ - ν := by
    rw [hY₃def, Affine.addY, Affine.negAddY, Affine.negY, hνdef, hX₃def, hX₁def]
    linear_combination -hFy
  rw [add_of_X_ne hx12]
  refine ⟨_, _, _, rfl, ?_, ?_⟩
  · change (v (W.toAffine.addX x₁ x₂ ℓ - x₀) * v (x₂ - x₀)) ^ 2 = v F₀
    rw [← hX₃def, ← hX₂def, ← hedef, hvX₃, sq, huu]
  · change v ((W.toAffine.addY x₁ x₂ y₁ ℓ - y₀) / (W.toAffine.addX x₁ x₂ ℓ - x₀)
        - (y₂ - y₀) / (x₂ - x₀)) = 1
    rw [← hX₃def, ← hY₃def, ← hX₂def]
    have hq : Y₃ / X₃ = -(ℓ + W.a₁) - ν / X₃ := by
      rw [hY₃, sub_div, mul_div_cancel_right₀ _ hX₃0]
    have ht₃ : Y₃ / X₃ - β = -((ℓ - α) + ν / X₃) := by
      rw [hq]; linear_combination -hsum
    have ht₂ : (y₂ - y₀) / X₂ - β = V₂ / X₂ := by
      rw [eq_div_iff hX₂0, sub_mul, div_mul_cancel₀ _ hX₂0, hV₂def, hX₂def]
    have hvt₃ : v (Y₃ / X₃ - β) < 1 := by
      rw [ht₃, Valuation.map_neg]
      refine Valuation.map_add_lt _ hvℓα ?_
      rw [map_div₀, div_lt_one₀ hvX₃0, hvν]; exact hu_lt_X₃
    have hvt₂ : v ((y₂ - y₀) / X₂ - β) = 1 := by
      rw [ht₂, map_div₀, hV₂, hedef, div_self (ne_of_gt he0)]
    have h : Y₃ / X₃ - (y₂ - y₀) / X₂ = (Y₃ / X₃ - β) - ((y₂ - y₀) / X₂ - β) := by ring
    rw [h, Valuation.map_sub_eq_of_lt_right _ (by rw [hvt₂]; exact hvt₃), hvt₂]
end Core

/-- 臨界側の曲線点では二方向の線形偏差が同じ付値uを持ち、u²=v(F₀)となる。
平方根を選ばず、実際の第一偏差の付値をuとして用いる。 -/
theorem critical_deviations (C : CriticalCentre A W) (D : TangentDirections C)
    {x y : K} (h : W.toAffine.Equation x y) (hX : v (x - C.x) < 1)
    (hanti : v (x - C.x) ^ 2 ≤ v (equationDefect W C.x C.y)) :
    ∃ u : A.ValueGroup,
      v (y - C.y - D.α * (x - C.x)) = u ∧ v (y - C.y - D.β * (x - C.x)) = u ∧
      u * u = v (equationDefect W C.x C.y) ∧ 0 < u ∧ v (x - C.x) ≤ u := by
  have hfpos : 0 < v (equationDefect W C.x C.y) := (Valuation.pos_iff _).mpr C.defect_ne_zero
  have hcube : v ((x - C.x) ^ 3) < v (equationDefect W C.x C.y) := by
    rw [map_pow, pow_succ]
    exact (mul_le_mul' hanti le_rfl).trans_lt (by simpa only [mul_one] using mul_lt_mul_of_pos_left hX hfpos)
  have hp : v (y - C.y - D.α * (x - C.x)) * v (y - C.y - D.β * (x - C.x)) =
      v (equationDefect W C.x C.y) := by
    rw [← map_mul, D.point_equation h, Valuation.map_sub_eq_of_lt_right _ hcube]
  have hd : v ((y - C.y - D.α * (x - C.x)) - (y - C.y - D.β * (x - C.x))) = v (x - C.x) := by
    rw [show (y - C.y - D.α * (x - C.x)) - (y - C.y - D.β * (x - C.x)) =
      (D.β - D.α) * (x - C.x) by ring, map_mul, Valuation.map_sub_swap, D.separated, one_mul]
  have heq : v (y - C.y - D.α * (x - C.x)) = v (y - C.y - D.β * (x - C.x)) := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hnval : v (y - C.y - D.β * (x - C.x)) = v (x - C.x) :=
        (Valuation.map_sub_eq_of_lt_right _ hlt).symm.trans hd
      have hpos : 0 < v (y - C.y - D.β * (x - C.x)) := by
        exact pos_of_mul_pos_right (hp ▸ hfpos) zero_le
      have hbad := mul_lt_mul_of_pos_right hlt hpos
      rw [hp, hnval, ← sq] at hbad
      exact (not_lt_of_ge hanti) hbad
    · have hmval : v (y - C.y - D.α * (x - C.x)) = v (x - C.x) :=
        (Valuation.map_sub_eq_of_lt_left _ hgt).symm.trans hd
      have hpos : 0 < v (y - C.y - D.α * (x - C.x)) := by
        exact pos_of_mul_pos_left (hp ▸ hfpos) zero_le
      have hbad := mul_lt_mul_of_pos_left hgt hpos
      rw [hp, hmval, ← sq] at hbad
      exact (not_lt_of_ge hanti) hbad
  have hs : v (y - C.y - D.α * (x - C.x)) * v (y - C.y - D.α * (x - C.x)) =
      v (equationDefect W C.x C.y) := by rwa [← heq] at hp
  refine ⟨_, rfl, heq.symm, hs, ?_, ?_⟩
  · exact pos_of_mul_pos_left (hs ▸ hfpos) zero_le
  · apply (pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp
    simpa only [sq, hs] using hanti

/-- 臨界側の点と浅い点の実際の和を構成し、深さの平方と浅い点に対する反対の枝を確定する。 -/
theorem critical_add_shallow [DecidableEq K] (C : CriticalCentre A W) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hanti : v (x₁ - C.x) ^ 2 ≤ v (equationDefect W C.x C.y))
    (hX₂ : v (x₂ - C.x) < 1) (hsh : v (equationDefect W C.x C.y) < v (x₂ - C.x) ^ 2) :
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      (v (x₃ - C.x) * v (x₂ - C.x)) ^ 2 = v (equationDefect W C.x C.y) ∧
      v (centreSlope C x₃ y₃ - centreSlope C x₂ y₂) = 1 := by
  obtain ⟨u, hm, hn, hs, hp, hx⟩ := critical_deviations C D h₁.1 hX₁ hanti
  have linear_near : ∀ γ : K, v (centreSlope C x₂ y₂ - γ) < 1 →
      v (y₂ - C.y - γ * (x₂ - C.x)) < v (x₂ - C.x) := by
    intro γ ht
    have he : y₂ - C.y - γ * (x₂ - C.x) = (centreSlope C x₂ y₂ - γ) * (x₂ - C.x) := by
      rw [sub_mul, centreSlope, div_mul_cancel₀ _ (shallow_x_ne C hsh)]
    rw [he, map_mul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right ht ((Valuation.pos_iff _).mpr (shallow_x_ne C hsh))
  rcases (slope_mem_and_branches_of_shallow D h₂.1 hX₂ hsh).2.2 with ha | hb
  · exact critical_shallow_core (W := W) (A := A) C.derivativeY D.sum_eq D.product_eq D.separated h₁ h₂
      (D.point_equation h₁.1) (D.point_equation h₂.1) hm hn hs hp hx hsh hX₂ (linear_near _ ha.1)
  · have hsep : v (D.β - D.α) = 1 := (Valuation.map_sub_swap _ _ _).trans D.separated
    exact critical_shallow_core (W := W) (A := A) C.derivativeY ((add_comm _ _).trans D.sum_eq)
      ((mul_comm _ _).trans D.product_eq) hsep h₁ h₂
      (by rw [mul_comm]; exact D.point_equation h₁.1) (by rw [mul_comm]; exact D.point_equation h₂.1)
      hn hm hs hp hx hsh hX₂ (linear_near _ hb.2)

end DkMath.Lib.NumberTheory.EllipticCriticalAddition
