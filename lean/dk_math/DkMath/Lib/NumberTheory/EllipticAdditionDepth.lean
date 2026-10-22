/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_level_add_of_branch_eq, blob 82120c24b217c48ebb7dbbc488d0dd94daf9d629.
Modified: arbitrary field, same DkMath centre/directions and existing shallow classification;
no re-selection of roots or upstream zero-component definitions.
-/

import DkMath.Lib.NumberTheory.EllipticBranchComparison
import DkMath.Lib.NumberTheory.EllipticDoublingDepth

#print "file: DkMath.Lib.NumberTheory.EllipticAdditionDepth"

/-!
# NOTE-031-002: 同じ枝の一般加法で深さと枝を同時に追う

E=v(X₁)v(X₂)、F=v(F₀)とすると、浅い同じ枝の和の深さはFとE²の比較で分岐する。
F<E²では深さEで枝を保ち、F=E²では臨界側へ移り、E²<FではN·E=Fで枝が反転する。
実際のPoint加法で有限の和を構成し、接線となる場合も含めて証明する。
相殺の閾値を等式に強めず、同じC,Dと曲線方程式を最後まで保持する。
-/
namespace DkMath.Lib.NumberTheory.EllipticAdditionDepth
open WeierstrassCurve Affine Affine.Point
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve K}
local notation "v" => A.valuation

/-- 同じ中心で曲線方程式を平行移動する。中心の非零のずれを残したまま使う。 -/
theorem translated_point (C : CriticalCentre A W) {x y : K} (h : W.toAffine.Equation x y) :
    (y - C.y) ^ 2 + W.a₁ * (x - C.x) * (y - C.y) =
      (x - C.x) ^ 3 + (W.a₂ + 3 * C.x) * (x - C.x) ^ 2 - equationDefect W C.x C.y := by
  have he := C.translated_equation (x - C.x) (y - C.y)
  rw [show C.x + (x - C.x) = x by ring, show C.y + (y - C.y) = y by ring] at he
  have hz : equationDefect W x y = 0 := sub_eq_zero.mpr ((Affine.equation_iff _ _).mp h)
  rw [hz] at he
  linear_combination -he

private theorem addX_formula (x₁ x₂ L : K) :
    W.toAffine.addX x₁ x₂ L = L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂ := rfl
private theorem addY_formula (x₁ x₂ y₁ L : K) :
    W.toAffine.addY x₁ x₂ y₁ L = -(L * (W.toAffine.addX x₁ x₂ L - x₁) + y₁) -
      W.a₁ * W.toAffine.addX x₁ x₂ L - W.a₃ := rfl

section cancel
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
private theorem lt_of_mul_lt_mul_right'' {a b c : Γ} (h : a * c < b * c) : a < b := by
  by_contra hle
  exact absurd h (not_lt.mpr (mul_le_mul' (not_lt.mp hle) le_rfl))
private theorem lt_of_mul_lt_mul_left'' {a b c : Γ} (h : c * a < c * b) : a < b := by
  by_contra hle
  exact absurd h (not_lt.mpr (mul_le_mul' le_rfl (not_lt.mp hle)))
private theorem le_of_mul_le_mul_right'' {a b c : Γ} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  by_contra hlt
  exact absurd h (not_le.mpr (mul_lt_mul_of_pos_right (not_le.mp hlt) hc))
private theorem le_of_mul_le_mul_left'' {a b c : Γ} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b := by
  by_contra hlt
  exact absurd h (not_le.mpr (mul_lt_mul_of_pos_left (not_le.mp hlt) hc))
end cancel
section Core
variable (A)
private theorem level_core {F₀ X₁ X₂ S u κ X₃ L n₃ τ₁ δ : K}
    (hX₁ : v X₁ < 1) (hX₂ : v X₂ < 1) (he₁ : v X₁ ≠ 0) (he₂ : v X₂ ≠ 0)
    (hsh₁ : v F₀ < v X₁ ^ 2) (hsh₂ : v F₀ < v X₂ ^ 2)
    (hS : v S ≤ max (v X₁) (v X₂)) (hu : v u = 1) (hδ : v δ = 1) (hτ₁ : v τ₁ < 1)
    (hκ : κ * u * (X₁ * X₂) = -((X₁ * X₂) ^ 2 + F₀ * S))
    (hV : X₁ * X₂ * X₃ = κ ^ 2 + F₀)
    (hLτ : L * X₁ = τ₁ * X₁ - κ)
    (hn₃ : n₃ = -L * X₃ - κ)
    (hcurve₃ : (n₃ + δ * X₃) * n₃ = X₃ ^ 3 - F₀) :
    v X₃ < 1 ∧
    (v F₀ < (v X₁ * v X₂) ^ 2 → v X₃ = v X₁ * v X₂ ∧ v ((n₃ + δ * X₃) / X₃ - τ₁) < 1) ∧
    (v F₀ = (v X₁ * v X₂) ^ 2 → v X₃ ^ 2 ≤ v F₀) ∧
    ((v X₁ * v X₂) ^ 2 < v F₀ →
      v X₃ * (v X₁ * v X₂) = v F₀ ∧ v ((n₃ + δ * X₃) / X₃ - τ₁) = 1) := by
  have he₁pos : 0 < v X₁ := zero_lt_iff.mpr he₁
  have he₂pos : 0 < v X₂ := zero_lt_iff.mpr he₂
  have hEpos : 0 < v X₁ * v X₂ := mul_pos he₁pos he₂pos
  have hE0 : v X₁ * v X₂ ≠ 0 := ne_of_gt hEpos
  have hEe₁ : v X₁ * v X₂ < v X₁ := by
    calc v X₁ * v X₂ < v X₁ * 1 := mul_lt_mul_of_pos_left hX₂ he₁pos
      _ = v X₁ := mul_one _
  have hE1 : v X₁ * v X₂ < 1 := hEe₁.trans hX₁
  have hvX₁X₂ : v (X₁ * X₂) = v X₁ * v X₂ := map_mul _ _ _
  have hS1 : v S < 1 := hS.trans_lt (max_lt hX₁ hX₂)
  have hfE : v F₀ < v X₁ * v X₂ := by
    rcases le_total (v X₁) (v X₂) with h | h
    · calc v F₀ < v X₁ ^ 2 := hsh₁
        _ = v X₁ * v X₁ := sq _
        _ ≤ v X₁ * v X₂ := mul_le_mul' le_rfl h
    · calc v F₀ < v X₂ ^ 2 := hsh₂
        _ = v X₂ * v X₂ := sq _
        _ ≤ v X₁ * v X₂ := mul_le_mul' h le_rfl
  have hfS₁ : v F₀ * v S < v X₁ * (v X₁ * v X₂) := by
    rcases le_total (v X₁) (v X₂) with h | h
    · have hS' : v S ≤ v X₂ := hS.trans (max_le h le_rfl)
      calc v F₀ * v S ≤ v F₀ * v X₂ := mul_le_mul' le_rfl hS'
        _ < v X₁ ^ 2 * v X₂ := mul_lt_mul_of_pos_right hsh₁ he₂pos
        _ = v X₁ * (v X₁ * v X₂) := by rw [sq, mul_assoc]
    · have hS' : v S ≤ v X₁ := hS.trans (max_le le_rfl h)
      calc v F₀ * v S ≤ v F₀ * v X₁ := mul_le_mul' le_rfl hS'
        _ < (v X₁ * v X₂) * v X₁ := mul_lt_mul_of_pos_right hfE he₁pos
        _ = v X₁ * (v X₁ * v X₂) := mul_comm _ _
  have hfSS : v F₀ * v S * v S < (v X₁ * v X₂) * (v X₁ * v X₂) := by
    rcases le_total (v X₁) (v X₂) with h | h
    · have hS' : v S ≤ v X₂ := hS.trans (max_le h le_rfl)
      calc v F₀ * v S * v S ≤ v F₀ * v X₂ * v X₂ := mul_le_mul' (mul_le_mul' le_rfl hS') hS'
        _ = v F₀ * (v X₂ * v X₂) := mul_assoc _ _ _
        _ < v X₁ ^ 2 * (v X₂ * v X₂) := mul_lt_mul_of_pos_right hsh₁ (mul_pos he₂pos he₂pos)
        _ = (v X₁ * v X₂) * (v X₁ * v X₂) := by rw [sq, mul_mul_mul_comm]
    · have hS' : v S ≤ v X₁ := hS.trans (max_le le_rfl h)
      calc v F₀ * v S * v S ≤ v F₀ * v X₁ * v X₁ := mul_le_mul' (mul_le_mul' le_rfl hS') hS'
        _ = v F₀ * (v X₁ * v X₁) := mul_assoc _ _ _
        _ < v X₂ ^ 2 * (v X₁ * v X₁) := mul_lt_mul_of_pos_right hsh₂ (mul_pos he₁pos he₁pos)
        _ = (v X₁ * v X₂) * (v X₁ * v X₂) := by rw [sq, mul_mul_mul_comm, mul_comm (v X₂) (v X₁)]
  have hsum_le : v ((X₁ * X₂) ^ 2 + F₀ * S) ≤ max ((v X₁ * v X₂) ^ 2) (v F₀ * v S) := by
    refine (Valuation.map_add _ _ _).trans ?_
    rw [map_pow, hvX₁X₂, map_mul]
  have hκE : v κ * (v X₁ * v X₂) = v ((X₁ * X₂) ^ 2 + F₀ * S) := by
    have h := congrArg (v) hκ
    rw [map_mul, map_mul, hu, mul_one, hvX₁X₂, Valuation.map_neg] at h
    exact h
  have hVv : (v X₁ * v X₂) * v X₃ = v (κ ^ 2 + F₀) := by
    have h := congrArg (v) hV
    rw [map_mul, hvX₁X₂] at h
    exact h
  have hκe₁ : v κ < v X₁ := by
    have h1 : v κ * (v X₁ * v X₂) < v X₁ * (v X₁ * v X₂) := by
      rw [hκE]
      refine hsum_le.trans_lt (max_lt ?_ hfS₁)
      rw [sq]
      exact mul_lt_mul_of_pos_right hEe₁ hEpos
    exact lt_of_mul_lt_mul_right'' h1
  have hL : v L < 1 := by
    have h1 : v (L * X₁) < v X₁ := by
      rw [hLτ]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hκe₁)
      rw [map_mul]
      calc v τ₁ * v X₁ < 1 * v X₁ := mul_lt_mul_of_pos_right hτ₁ he₁pos
        _ = v X₁ := one_mul _
    rw [map_mul] at h1
    exact lt_of_mul_lt_mul_right'' (by rw [one_mul]; exact h1)
  have clause_i : v F₀ < (v X₁ * v X₂) ^ 2 →
      v X₃ = v X₁ * v X₂ ∧ v ((n₃ + δ * X₃) / X₃ - τ₁) < 1 := by
    intro hi
    have hFS : v (F₀ * S) < v ((X₁ * X₂) ^ 2) := by
      rw [map_mul, map_pow, hvX₁X₂]
      calc v F₀ * v S ≤ v F₀ * 1 := mul_le_mul' le_rfl hS1.le
        _ = v F₀ := mul_one _
        _ < (v X₁ * v X₂) ^ 2 := hi
    have hs : v ((X₁ * X₂) ^ 2 + F₀ * S) = (v X₁ * v X₂) ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ hFS, map_pow, hvX₁X₂]
    have hvκ : v κ = v X₁ * v X₂ := mul_right_cancel₀ hE0 (by rw [hκE, hs, sq])
    have hk2 : v F₀ < v (κ ^ 2) := by rw [map_pow, hvκ]; exact hi
    have hX₃ : v X₃ = v X₁ * v X₂ :=
      mul_left_cancel₀ hE0 (by rw [hVv, Valuation.map_add_eq_of_lt_left _ hk2, map_pow, hvκ, sq])
    refine ⟨hX₃, ?_⟩
    have hX₃pos : 0 < v X₃ := by rw [hX₃]; exact hEpos
    have hn₃v : v n₃ = v X₁ * v X₂ := by
      have hlt : v (L * X₃) < v κ := by
        rw [map_mul, hX₃, hvκ]
        calc v L * (v X₁ * v X₂) < 1 * (v X₁ * v X₂) := mul_lt_mul_of_pos_right hL hEpos
          _ = v X₁ * v X₂ := one_mul _
      rw [hn₃, show -L * X₃ - κ = -(L * X₃ + κ) by ring, Valuation.map_neg,
        Valuation.map_add_eq_of_lt_right _ hlt, hvκ]
    have hm₃v : v (n₃ + δ * X₃) < v X₁ * v X₂ := by
      have h1 : v ((n₃ + δ * X₃) * n₃) < (v X₁ * v X₂) * (v X₁ * v X₂) := by
        rw [hcurve₃]
        refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
        · rw [map_pow, hX₃]
          calc (v X₁ * v X₂) ^ 3 = (v X₁ * v X₂) * (v X₁ * v X₂) * (v X₁ * v X₂) := by
                rw [pow_succ, sq]
            _ < (v X₁ * v X₂) * (v X₁ * v X₂) * 1 :=
                mul_lt_mul_of_pos_left hE1 (mul_pos hEpos hEpos)
            _ = (v X₁ * v X₂) * (v X₁ * v X₂) := mul_one _
        · rw [← sq]; exact hi
      rw [map_mul, hn₃v] at h1
      exact lt_of_mul_lt_mul_right'' h1
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hτ₁)
    rw [map_div₀, hX₃, div_lt_one₀ hEpos]
    exact hm₃v
  have clause_ii : v F₀ = (v X₁ * v X₂) ^ 2 → v X₃ ^ 2 ≤ v F₀ := by
    intro hii
    have hf0 : v F₀ ≠ 0 := by rw [hii]; exact pow_ne_zero 2 hE0
    have hFS : v (F₀ * S) < v ((X₁ * X₂) ^ 2) := by
      rw [map_mul, map_pow, hvX₁X₂, ← hii]
      calc v F₀ * v S < v F₀ * 1 := mul_lt_mul_of_pos_left hS1 (zero_lt_iff.mpr hf0)
        _ = v F₀ := mul_one _
    have hs : v ((X₁ * X₂) ^ 2 + F₀ * S) = (v X₁ * v X₂) ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ hFS, map_pow, hvX₁X₂]
    have hvκ : v κ = v X₁ * v X₂ := mul_right_cancel₀ hE0 (by rw [hκE, hs, sq])
    have h1 : (v X₁ * v X₂) * v X₃ ≤ (v X₁ * v X₂) * (v X₁ * v X₂) := by
      rw [hVv]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_pow, hvκ, sq]
      · rw [hii, sq]
    have hX₃le : v X₃ ≤ v X₁ * v X₂ := le_of_mul_le_mul_left'' hEpos h1
    calc v X₃ ^ 2 = v X₃ * v X₃ := sq _
      _ ≤ (v X₁ * v X₂) * (v X₁ * v X₂) := mul_le_mul' hX₃le hX₃le
      _ = (v X₁ * v X₂) ^ 2 := (sq _).symm
      _ = v F₀ := hii.symm
  have clause_iii : (v X₁ * v X₂) ^ 2 < v F₀ →
      v X₃ * (v X₁ * v X₂) = v F₀ ∧ v ((n₃ + δ * X₃) / X₃ - τ₁) = 1 := by
    intro hiii
    have hfpos : 0 < v F₀ := lt_of_le_of_lt zero_le hiii
    have hf0 : v F₀ ≠ 0 := ne_of_gt hfpos
    have hk2 : v (κ ^ 2) < v F₀ := by
      rcases le_or_gt (v F₀ * v S) ((v X₁ * v X₂) ^ 2) with hc | hc
      · have h1 : v κ * (v X₁ * v X₂) ≤ (v X₁ * v X₂) * (v X₁ * v X₂) := by
          rw [hκE, ← sq]; exact hsum_le.trans (max_le le_rfl hc)
        have h2 : v κ ≤ v X₁ * v X₂ := le_of_mul_le_mul_right'' hEpos h1
        calc v (κ ^ 2) = v κ * v κ := by rw [map_pow, sq]
          _ ≤ (v X₁ * v X₂) * (v X₁ * v X₂) := mul_le_mul' h2 h2
          _ = (v X₁ * v X₂) ^ 2 := (sq _).symm
          _ < v F₀ := hiii
      · have h1 : v κ * (v X₁ * v X₂) ≤ v F₀ * v S := by
          rw [hκE]; exact hsum_le.trans (max_le hc.le le_rfl)
        have h2 : (v κ * (v X₁ * v X₂)) * (v κ * (v X₁ * v X₂)) ≤ (v F₀ * v S) * (v F₀ * v S) :=
          mul_le_mul' h1 h1
        have h3 : (v F₀ * v S) * (v F₀ * v S) < v F₀ * ((v X₁ * v X₂) * (v X₁ * v X₂)) := by
          rw [show (v F₀ * v S) * (v F₀ * v S) = v F₀ * (v F₀ * v S * v S) by
            simp only [mul_assoc, mul_left_comm (v S) (v F₀) (v S)]]
          exact mul_lt_mul_of_pos_left hfSS hfpos
        have h4 : (v κ * v κ) * ((v X₁ * v X₂) * (v X₁ * v X₂))
            < v F₀ * ((v X₁ * v X₂) * (v X₁ * v X₂)) := by
          calc (v κ * v κ) * ((v X₁ * v X₂) * (v X₁ * v X₂))
                = (v κ * (v X₁ * v X₂)) * (v κ * (v X₁ * v X₂)) := mul_mul_mul_comm _ _ _ _
            _ ≤ (v F₀ * v S) * (v F₀ * v S) := h2
            _ < v F₀ * ((v X₁ * v X₂) * (v X₁ * v X₂)) := h3
        rw [map_pow, sq]
        exact lt_of_mul_lt_mul_right'' h4
    have hsumv : v (κ ^ 2 + F₀) = v F₀ := Valuation.map_add_eq_of_lt_right _ hk2
    have hX₃ : v X₃ * (v X₁ * v X₂) = v F₀ := by rw [mul_comm, hVv, hsumv]
    refine ⟨hX₃, ?_⟩
    have hX₃0' : v X₃ ≠ 0 := fun h => hf0 (by rw [← hX₃, h, zero_mul])
    have hX₃pos : 0 < v X₃ := zero_lt_iff.mpr hX₃0'
    have hX₃0 : X₃ ≠ 0 := (Valuation.ne_zero_iff _).mp hX₃0'
    have hκX₃ : v κ < v X₃ := by
      have h1 : v κ * (v X₁ * v X₂) < v X₃ * (v X₁ * v X₂) := by
        rw [hX₃, hκE]
        refine hsum_le.trans_lt (max_lt hiii ?_)
        calc v F₀ * v S < v F₀ * 1 := mul_lt_mul_of_pos_left hS1 hfpos
          _ = v F₀ := mul_one _
      exact lt_of_mul_lt_mul_right'' h1
    have hn₃v : v n₃ < v X₃ := by
      rw [hn₃, show -L * X₃ - κ = -(L * X₃ + κ) by ring, Valuation.map_neg]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hκX₃)
      rw [map_mul]
      calc v L * v X₃ < 1 * v X₃ := mul_lt_mul_of_pos_right hL hX₃pos
        _ = v X₃ := one_mul _
    have hsplit : (n₃ + δ * X₃) / X₃ - τ₁ = (n₃ / X₃ - τ₁) + δ := by
      field_simp
      ring
    have hsmall : v (n₃ / X₃ - τ₁) < v δ := by
      rw [hδ]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hτ₁)
      rw [map_div₀, div_lt_one₀ hX₃pos]
      exact hn₃v
    rw [hsplit, Valuation.map_add_eq_of_lt_right _ hsmall, hδ]
  refine ⟨?_, clause_i, clause_ii, clause_iii⟩
  rcases lt_trichotomy (v F₀) ((v X₁ * v X₂) ^ 2) with h | h | h
  · rw [(clause_i h).1]; exact hE1
  · have h2 := clause_ii h
    by_contra hge
    rw [not_lt] at hge
    have h3 : (1 : A.ValueGroup) ≤ v X₃ ^ 2 := by
      calc (1 : A.ValueGroup) = 1 * 1 := (mul_one 1).symm
        _ ≤ v X₃ * v X₃ := mul_le_mul' hge hge
        _ = v X₃ ^ 2 := (sq _).symm
    exact absurd ((h3.trans h2).trans_lt (hfE.trans hE1)) (lt_irrefl 1)
  · have h1 := (clause_iii h).1
    have h2 : v X₃ * (v X₁ * v X₂) < 1 * (v X₁ * v X₂) := by rw [h1, one_mul]; exact hfE
    exact lt_of_mul_lt_mul_right'' h2
end Core

/-- 浅い同じ枝の二点の実際の和を構成し、深さと枝の三つの遷移を返す。
同じX座標では接線の非零分母を供給し、異なるX座標では弦の分母を約分する。
閾値の等号では臨界側の不等式だけを保持する。 -/
theorem same_branch_add [DecidableEq K] (C : CriticalCentre A W) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hsh₁ : v (equationDefect W C.x C.y) < v (x₁ - C.x) ^ 2)
    (hsh₂ : v (equationDefect W C.x C.y) < v (x₂ - C.x) ^ 2)
    (hbr : v ((y₁ - C.y) / (x₁ - C.x) - (y₂ - C.y) / (x₂ - C.x)) < 1) :
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 ∧
      (v (equationDefect W C.x C.y)
          < (v (x₁ - C.x) * v (x₂ - C.x)) ^ 2 →
        v (x₃ - C.x) = v (x₁ - C.x) * v (x₂ - C.x) ∧
        v ((y₃ - C.y) / (x₃ - C.x) - (y₁ - C.y) / (x₁ - C.x)) < 1) ∧
      (v (equationDefect W C.x C.y)
          = (v (x₁ - C.x) * v (x₂ - C.x)) ^ 2 →
        v (x₃ - C.x) ^ 2 ≤
          v (equationDefect W C.x C.y)) ∧
      ((v (x₁ - C.x) * v (x₂ - C.x)) ^ 2
          < v (equationDefect W C.x C.y) →
        v (x₃ - C.x) * (v (x₁ - C.x) * v (x₂ - C.x)) =
          v (equationDefect W C.x C.y) ∧
        v ((y₃ - C.y) / (x₃ - C.x) - (y₁ - C.y) / (x₁ - C.x)) = 1) := by
  classical
  have hFy := C.derivativeY
  have hFx := sub_eq_zero.mp C.derivativeX
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : K, F₀ = equationDefect W C.x C.y := ⟨_, rfl⟩
  rw [← hF₀] at hsh₁ hsh₂ ⊢
  let α := D.α
  let β := D.β
  have hsum := D.sum_eq
  have hprod := D.product_eq
  have hαβ := D.separated
  have he₁ : v (x₁ - C.x) ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at hsh₁; exact absurd hsh₁ (not_lt.mpr zero_le)
  have he₂ : v (x₂ - C.x) ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at hsh₂; exact absurd hsh₂ (not_lt.mpr zero_le)
  have hX₁0 : x₁ - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp he₁
  have hX₂0 : x₂ - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp he₂
  have hfr₁ := translated_point C h₁.1
  have hfr₂ := translated_point C h₂.1
  rw [← hF₀] at hfr₁ hfr₂
  have main : ∀ {γ γ' : K}, γ + γ' = -W.a₁ →
      γ * γ' = -(W.a₂ + 3 * C.x) → v (γ - γ') = 1 →
      v ((y₁ - C.y) - γ * (x₁ - C.x)) < v (x₁ - C.x) →
      ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 ∧
      (v F₀ < (v (x₁ - C.x) * v (x₂ - C.x)) ^ 2 →
        v (x₃ - C.x) = v (x₁ - C.x) * v (x₂ - C.x) ∧
        v ((y₃ - C.y) / (x₃ - C.x) - (y₁ - C.y) / (x₁ - C.x)) < 1) ∧
      (v F₀ = (v (x₁ - C.x) * v (x₂ - C.x)) ^ 2 → v (x₃ - C.x) ^ 2 ≤ v F₀) ∧
      ((v (x₁ - C.x) * v (x₂ - C.x)) ^ 2 < v F₀ →
        v (x₃ - C.x) * (v (x₁ - C.x) * v (x₂ - C.x)) = v F₀ ∧
        v ((y₃ - C.y) / (x₃ - C.x) - (y₁ - C.y) / (x₁ - C.x)) = 1) := by
    intro γ γ' hs hp hγγ' hm₁
    have hδ : v (γ' - γ) = 1 := by rw [Valuation.map_sub_swap]; exact hγγ'
    obtain ⟨τ₁, hτ₁d⟩ : ∃ τ₁ : K, τ₁ = (y₁ - C.y) / (x₁ - C.x) - γ := ⟨_, rfl⟩
    obtain ⟨τ₂, hτ₂d⟩ : ∃ τ₂ : K, τ₂ = (y₂ - C.y) / (x₂ - C.x) - γ := ⟨_, rfl⟩
    have hτ₁X : τ₁ * (x₁ - C.x) = (y₁ - C.y) - γ * (x₁ - C.x) := by
      rw [hτ₁d]; field_simp
    have hτ₂X : τ₂ * (x₂ - C.x) = (y₂ - C.y) - γ * (x₂ - C.x) := by
      rw [hτ₂d]; field_simp
    have hτ₁ : v τ₁ < 1 := by
      have h := hm₁
      rw [← hτ₁X, map_mul] at h
      exact lt_of_mul_lt_mul_right'' (by rw [one_mul]; exact h)
    have hτ₂ : v τ₂ < 1 := by
      have hid : τ₂ = τ₁ - ((y₁ - C.y) / (x₁ - C.x) - (y₂ - C.y) / (x₂ - C.x)) := by
        rw [hτ₁d, hτ₂d]; ring
      rw [hid]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hτ₁ hbr)
    obtain ⟨u, hud⟩ : ∃ u : K,
        u = (y₁ - C.y) / (x₁ - C.x) + (y₂ - C.y) / (x₂ - C.x) + W.a₁ := ⟨_, rfl⟩
    have hu_eq : u = (τ₁ + τ₂) + (γ - γ') := by
      rw [hud, hτ₁d, hτ₂d]; linear_combination hs
    have hvu : v u = 1 := by
      rw [hu_eq, Valuation.map_add_eq_of_lt_right _ (by
        rw [hγγ']; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hτ₁ hτ₂)), hγγ']
    have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvu]; exact one_ne_zero)
    have convert_t : ∀ {X₃ Y₃ n₃ : K}, X₃ ≠ 0 → n₃ = Y₃ - γ' * X₃ →
        (n₃ + (γ' - γ) * X₃) / X₃ - τ₁ = Y₃ / X₃ - (y₁ - C.y) / (x₁ - C.x) := by
      intro X₃ Y₃ n₃ hX₃0 hn
      rw [hn, hτ₁d]
      field_simp
      ring
    by_cases hx : x₁ = x₂
    · subst hx
      rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
      · subst hy
        have hY₁u : u * (x₁ - C.x) = 2 * (y₁ - C.y) + W.a₁ * (x₁ - C.x) := by
          rw [hud, add_mul, add_mul, div_mul_cancel₀ _ hX₁0]; ring
        have hΨ_eq : y₁ - W.toAffine.negY x₁ y₁ = u * (x₁ - C.x) := by
          rw [Affine.negY, hY₁u]
          linear_combination hFy
        have hΨ : y₁ ≠ W.toAffine.negY x₁ y₁ := by
          intro h0
          have : u * (x₁ - C.x) = 0 := by rw [← hΨ_eq, ← h0, sub_self]
          rcases mul_eq_zero.mp this with h' | h'
          · exact hu0 h'
          · exact hX₁0 h'
        rw [add_of_Y_ne hΨ]
        refine ⟨_, _, _, rfl, ?_⟩
        have h₃ := nonsingular_add h₁ h₂ fun hxy => hΨ hxy.2
        set L := W.toAffine.slope x₁ x₁ y₁ y₁ with hLd
        have hLeq : L = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)
            / (y₁ - W.toAffine.negY x₁ y₁) := slope_of_Y_ne rfl hΨ
        have hLΨ : L * (u * (x₁ - C.x)) = 3 * (x₁ - C.x) ^ 2 + 2 * (W.a₂
            + 3 * C.x) * (x₁ - C.x) - W.a₁ * (y₁ - C.y) := by
          have hden : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hΨ
          have h1 : L * (y₁ - W.toAffine.negY x₁ y₁)
              = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
            rw [hLeq, div_mul_cancel₀ _ hden]
          change L * (y₁ - W.toAffine.negY x₁ y₁) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ at h1
          rw [hΨ_eq] at h1
          linear_combination h1 - hFx
        obtain ⟨κ, hκd⟩ : ∃ κ : K, κ = (y₁ - C.y) - L * (x₁ - C.x) := ⟨_, rfl⟩
        have hx₃ : W.toAffine.addX x₁ x₁ L - C.x = L ^ 2 + W.a₁ * L
            - (W.a₂ + 3 * C.x) - (x₁ - C.x) - (x₁ - C.x) := by
          rw [addX_formula]; ring
        have hy₃ : W.toAffine.addY x₁ x₁ y₁ L - C.y
            = -L * ((W.toAffine.addX x₁ x₁ L - C.x) - (x₁ - C.x)) - (y₁ - C.y)
              - W.a₁ * (W.toAffine.addX x₁ x₁ L - C.x) := by
          rw [addY_formula]; linear_combination -hFy
        have hκ : κ * u * ((x₁ - C.x) * (x₁ - C.x))
            = -(((x₁ - C.x) * (x₁ - C.x)) ^ 2 + F₀ * ((x₁ - C.x) + (x₁ - C.x))) := by
          have h1 : κ * (u * (x₁ - C.x)) = -((x₁ - C.x) ^ 3 + 2 * F₀) := by
            rw [hY₁u]
            rw [hY₁u] at hLΨ
            linear_combination 2 * hfr₁ - (x₁ - C.x) * hLΨ + (2 * (y₁ - C.y)
              + W.a₁ * (x₁ - C.x)) * hκd
          linear_combination (x₁ - C.x) * h1
        have hV : (x₁ - C.x) * (x₁ - C.x) * (W.toAffine.addX x₁ x₁ L - C.x) = κ ^ 2 + F₀ := by
          rw [hx₃]
          rw [hY₁u] at hLΨ
          linear_combination -hfr₁ + (x₁ - C.x) * hLΨ - (κ + (y₁ - C.y) - L * (x₁ - C.x)) * hκd
        have hLτ : (L - γ) * (x₁ - C.x) = τ₁ * (x₁ - C.x) - κ := by
          rw [hτ₁X, hκd]; ring
        obtain ⟨n₃, hn₃d⟩ : ∃ n₃ : K, n₃ = (W.toAffine.addY x₁ x₁ y₁ L - C.y)
            - γ' * (W.toAffine.addX x₁ x₁ L - C.x) := ⟨_, rfl⟩
        have hn₃ : n₃ = -(L - γ) * (W.toAffine.addX x₁ x₁ L - C.x) - κ := by
          rw [hn₃d, hy₃, hκd]
          linear_combination -(W.toAffine.addX x₁ x₁ L - C.x) * hs
        have hfr₃ := translated_point C h₃.1
        rw [← hF₀] at hfr₃
        have hcurve₃ : (n₃ + (γ' - γ) * (W.toAffine.addX x₁ x₁ L - C.x)) * n₃
            = (W.toAffine.addX x₁ x₁ L - C.x) ^ 3 - F₀ := by
          rw [hn₃d]
          linear_combination hfr₃ - (W.toAffine.addX x₁ x₁ L - C.x)
            * (W.toAffine.addY x₁ x₁ y₁ L - C.y) * hs
            + (W.toAffine.addX x₁ x₁ L - C.x) ^ 2 * hp
        have hS : v ((x₁ - C.x) + (x₁ - C.x)) ≤ max (v (x₁ - C.x)) (v (x₁ - C.x)) :=
          Valuation.map_add _ _ _
        obtain ⟨hlt, hi, hii, hiii⟩ := level_core A hX₁ hX₁ he₁ he₁ hsh₁ hsh₁ hS hvu hδ hτ₁
          hκ hV hLτ hn₃ hcurve₃
        refine ⟨hlt, fun hf => ?_, hii, fun hf => ?_⟩
        · obtain ⟨hX₃, hb⟩ := hi hf
          have hX₃0 : W.toAffine.addX x₁ x₁ L - C.x ≠ 0 :=
            (Valuation.ne_zero_iff _).mp (by rw [hX₃]; exact mul_ne_zero he₁ he₁)
          rw [convert_t hX₃0 hn₃d] at hb
          exact ⟨hX₃, hb⟩
        · obtain ⟨hX₃, hb⟩ := hiii hf
          have hvX₃0 : v (W.toAffine.addX x₁ x₁ L - C.x) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hX₃
            exact absurd hf (by rw [← hX₃]; exact not_lt.mpr zero_le)
          have hX₃0 : W.toAffine.addX x₁ x₁ L - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp hvX₃0
          rw [convert_t hX₃0 hn₃d] at hb
          exact ⟨hX₃, hb⟩
      · exfalso
        have h1 : u * (x₁ - C.x) = (y₁ - C.y) + (y₂ - C.y) + W.a₁ * (x₁ - C.x) := by
          rw [hud, add_mul, add_mul, div_mul_cancel₀ _ hX₁0, div_mul_cancel₀ _ hX₁0]
        rw [hy, Affine.negY] at h1
        have h2 : u * (x₁ - C.x) = 0 := by rw [h1]; linear_combination -hFy
        rcases mul_eq_zero.mp h2 with h | h
        · exact hu0 h
        · exact hX₁0 h
    · rw [add_of_X_ne hx]
      refine ⟨_, _, _, rfl, ?_⟩
      have h₃ := nonsingular_add h₁ h₂ fun hxy => hx hxy.1
      set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hLd
      have hD0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hLD : L * ((x₁ - C.x) - (x₂ - C.x)) = (y₁ - C.y) - (y₂ - C.y) := by
        rw [hLd, slope_of_X_ne hx]; field_simp; ring
      obtain ⟨κ, hκd⟩ : ∃ κ : K, κ = (y₁ - C.y) - L * (x₁ - C.x) := ⟨_, rfl⟩
      have hx₃ : W.toAffine.addX x₁ x₂ L - C.x = L ^ 2 + W.a₁ * L
          - (W.a₂ + 3 * C.x) - (x₁ - C.x) - (x₂ - C.x) := by
        rw [addX_formula]; ring
      have hy₃ : W.toAffine.addY x₁ x₂ y₁ L - C.y
          = -L * ((W.toAffine.addX x₁ x₂ L - C.x) - (x₁ - C.x)) - (y₁ - C.y)
            - W.a₁ * (W.toAffine.addX x₁ x₂ L - C.x) := by
        rw [addY_formula]; linear_combination -hFy
      have hu_mul : u * ((x₁ - C.x) * (x₂ - C.x)) = (y₁ - C.y) * (x₂ - C.x) + (y₂ - C.y) * (x₁ - C.x)
          + W.a₁ * ((x₁ - C.x) * (x₂ - C.x)) := by
        rw [hud]; field_simp
      have hκ : κ * u * ((x₁ - C.x) * (x₂ - C.x))
          = -(((x₁ - C.x) * (x₂ - C.x)) ^ 2 + F₀ * ((x₁ - C.x) + (x₂ - C.x))) := by
        have key : ((x₁ - C.x) - (x₂ - C.x)) * (κ * ((y₁ - C.y) * (x₂ - C.x) + (y₂ - C.y) * (x₁ - C.x)
            + W.a₁ * ((x₁ - C.x) * (x₂ - C.x)))
            + (((x₁ - C.x) * (x₂ - C.x)) ^ 2 + F₀ * ((x₁ - C.x) + (x₂ - C.x)))) = 0 := by
          rw [hκd]
          linear_combination (-(x₂ - C.x) ^ 2) * hfr₁ + (x₁ - C.x) ^ 2 * hfr₂
            + (-((x₁ - C.x) * ((x₁ - C.x) * (x₂ - C.x) * W.a₁
              + (x₁ - C.x) * (y₂ - C.y) + (x₂ - C.x) * (y₁ - C.y)))) * hLD
        have hD0' : (x₁ - C.x) - (x₂ - C.x) ≠ 0 := by rw [sub_sub_sub_cancel_right]; exact hD0
        have key' := (mul_eq_zero.mp key).resolve_left hD0'
        rw [mul_assoc, hu_mul]
        linear_combination key'
      have hV : (x₁ - C.x) * (x₂ - C.x) * (W.toAffine.addX x₁ x₂ L - C.x) = κ ^ 2 + F₀ := by
        have key : ((x₁ - C.x) - (x₂ - C.x)) ^ 2 * ((x₁ - C.x) * (x₂ - C.x)
            * (W.toAffine.addX x₁ x₂ L - C.x) - (κ ^ 2 + F₀)) = 0 := by
          rw [hx₃, hκd]
          linear_combination ((x₂ - C.x) * ((x₁ - C.x) - (x₂ - C.x))) * hfr₁
            - ((x₁ - C.x) * ((x₁ - C.x) - (x₂ - C.x))) * hfr₂
            + ((x₁ - C.x) * ((x₁ - C.x) - (x₂ - C.x)) * (-L * ((x₁ - C.x) - (x₂ - C.x))
              + W.a₁ * (x₂ - C.x) + (y₁ - C.y) + (y₂ - C.y))) * hLD
        have hD0' : ((x₁ - C.x) - (x₂ - C.x)) ^ 2 ≠ 0 := by
          rw [sub_sub_sub_cancel_right]; exact pow_ne_zero 2 hD0
        exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hD0')
      have hLτ : (L - γ) * (x₁ - C.x) = τ₁ * (x₁ - C.x) - κ := by
        rw [hτ₁X, hκd]; ring
      obtain ⟨n₃, hn₃d⟩ : ∃ n₃ : K, n₃ = (W.toAffine.addY x₁ x₂ y₁ L - C.y)
          - γ' * (W.toAffine.addX x₁ x₂ L - C.x) := ⟨_, rfl⟩
      have hn₃ : n₃ = -(L - γ) * (W.toAffine.addX x₁ x₂ L - C.x) - κ := by
        rw [hn₃d, hy₃, hκd]
        linear_combination -(W.toAffine.addX x₁ x₂ L - C.x) * hs
      have hfr₃ := translated_point C h₃.1
      rw [← hF₀] at hfr₃
      have hcurve₃ : (n₃ + (γ' - γ) * (W.toAffine.addX x₁ x₂ L - C.x)) * n₃
          = (W.toAffine.addX x₁ x₂ L - C.x) ^ 3 - F₀ := by
        rw [hn₃d]
        linear_combination hfr₃ - (W.toAffine.addX x₁ x₂ L - C.x)
          * (W.toAffine.addY x₁ x₂ y₁ L - C.y) * hs
          + (W.toAffine.addX x₁ x₂ L - C.x) ^ 2 * hp
      have hS : v ((x₁ - C.x) + (x₂ - C.x)) ≤ max (v (x₁ - C.x)) (v (x₂ - C.x)) :=
        Valuation.map_add _ _ _
      obtain ⟨hlt, hi, hii, hiii⟩ := level_core A hX₁ hX₂ he₁ he₂ hsh₁ hsh₂ hS hvu hδ hτ₁
        hκ hV hLτ hn₃ hcurve₃
      refine ⟨hlt, fun hf => ?_, hii, fun hf => ?_⟩
      · obtain ⟨hX₃, hb⟩ := hi hf
        have hX₃0 : W.toAffine.addX x₁ x₂ L - C.x ≠ 0 :=
          (Valuation.ne_zero_iff _).mp (by rw [hX₃]; exact mul_ne_zero he₁ he₂)
        rw [convert_t hX₃0 hn₃d] at hb
        exact ⟨hX₃, hb⟩
      · obtain ⟨hX₃, hb⟩ := hiii hf
        have hvX₃0 : v (W.toAffine.addX x₁ x₂ L - C.x) ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hX₃
          exact absurd hf (by rw [← hX₃]; exact not_lt.mpr zero_le)
        have hX₃0 : W.toAffine.addX x₁ x₂ L - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp hvX₃0
        rw [convert_t hX₃0 hn₃d] at hb
        exact ⟨hX₃, hb⟩
  have linear_near : ∀ γ : K, v (centreSlope C x₁ y₁ - γ) < 1 →
      v ((y₁ - C.y) - γ * (x₁ - C.x)) < v (x₁ - C.x) := by
    intro γ ht
    have he : (y₁ - C.y) - γ * (x₁ - C.x) = (centreSlope C x₁ y₁ - γ) * (x₁ - C.x) := by
      rw [sub_mul, centreSlope, div_mul_cancel₀ _ hX₁0]
    rw [he, map_mul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right ht ((Valuation.pos_iff _).mpr hX₁0)
  rcases (slope_mem_and_branches_of_shallow D h₁.1 hX₁ (hF₀ ▸ hsh₁)).2.2 with ha | hb
  · exact main hsum hprod hαβ (linear_near α ha.1)
  · have hsum' : β + α = -W.a₁ := (add_comm _ _).trans hsum
    have hprod' : β * α = -(W.a₂ + 3 * C.x) := (mul_comm _ _).trans hprod
    have hβα : v (β - α) = 1 := (Valuation.map_sub_swap _ _ _).trans hαβ
    exact main hsum' hprod' hβα (linear_near β hb.2)

end DkMath.Lib.NumberTheory.EllipticAdditionDepth
