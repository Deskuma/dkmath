/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Chord deviation comparison adapted from S_WeierstrassCurve_inZeroComponentAt_add_of_antipodal,
blob 5e3cb7b635d90a3e089f4bf18d1b4c851641b746.
Modified: same DkMath C,D and critical deviations; tangent case reconstructed from the
existing doubling numerator valuation instead of upstream tangent_core.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalAddition

#print "file: DkMath.Lib.NumberTheory.EllipticCriticalPair"

/-!
# NOTE-031-002: 臨界側の二点の和は滑らかに還元する

二点の二方向への偏差の付値は等しい。弦の偏差の差にも同じ性質が輸送される。
同一点の接線は既存の倍点分子の最大値則へ帰着し、別の長い接線評価を導入しない。
整モデルと一般ファイバーの一致を保ち、HasSmoothReductionという実装済みの条件を返す。
-/
namespace DkMath.Lib.NumberTheory.EllipticCriticalPair
open WeierstrassCurve Affine Affine.Point EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticCriticalDepth EllipticDoublingDepth EllipticCriticalAddition
open EllipticGoodReductionSeparation EllipticNodalReduction EllipticBranchComparison
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve K}
local notation "v" => A.valuation
private theorem depth_le_deviations {C : CriticalCentre A W} (D : TangentDirections C)
    (x y : K) {m : A.ValueGroup}
    (hm : v (y - C.y - D.α * (x - C.x)) ≤ m) (hn : v (y - C.y - D.β * (x - C.x)) ≤ m) :
    v (x - C.x) ≤ m := by
  have he : (y - C.y - D.α * (x - C.x)) - (y - C.y - D.β * (x - C.x)) =
      (D.β - D.α) * (x - C.x) := by ring
  have hv := Valuation.map_sub v (y - C.y - D.α * (x - C.x)) (y - C.y - D.β * (x - C.x))
  rw [he, map_mul, Valuation.map_sub_swap, D.separated, one_mul] at hv
  exact hv.trans (max_le hm hn)

private theorem equal_deviation_differences (C : CriticalCentre A W) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    {m : A.ValueGroup} (hm1 : m < 1)
    (hs₁ : v ((y₁ - C.y) - D.α * (x₁ - C.x)) = m) (ht₁ : v ((y₁ - C.y) - D.β * (x₁ - C.x)) = m)
    (hs₂ : v ((y₂ - C.y) - D.α * (x₂ - C.x)) = m) (ht₂ : v ((y₂ - C.y) - D.β * (x₂ - C.x)) = m) :
    v ((y₁ - y₂) - D.α * (x₁ - x₂)) = v ((y₁ - y₂) - D.β * (x₁ - x₂)) := by
  set s₁ := (y₁ - C.y) - D.α * (x₁ - C.x) with hs₁_def
  set t₁ := (y₁ - C.y) - D.β * (x₁ - C.x) with ht₁_def
  set s₂ := (y₂ - C.y) - D.α * (x₂ - C.x) with hs₂_def
  set t₂ := (y₂ - C.y) - D.β * (x₂ - C.x) with ht₂_def
  set F₀ := equationDefect W C.x C.y with hF₀_def
  have hds : (y₁ - y₂) - D.α * (x₁ - x₂) = s₁ - s₂ := by ring
  have hdt : (y₁ - y₂) - D.β * (x₁ - x₂) = t₁ - t₂ := by ring
  rw [hds, hdt]
  by_cases hm0 : m = 0
  · have e₁ : s₁ = 0 := (Valuation.zero_iff _).mp (hs₁.trans hm0)
    have e₂ : s₂ = 0 := (Valuation.zero_iff _).mp (hs₂.trans hm0)
    have e₃ : t₁ = 0 := (Valuation.zero_iff _).mp (ht₁.trans hm0)
    have e₄ : t₂ = 0 := (Valuation.zero_iff _).mp (ht₂.trans hm0)
    rw [e₁, e₂, e₃, e₄]
  have hm_pos : 0 < m := lt_of_le_of_ne zero_le (Ne.symm hm0)
  have hst₁ : s₁ * t₁ = (x₁ - C.x) ^ 3 - F₀ := D.point_equation h₁
  have hst₂ : s₂ * t₂ = (x₂ - C.x) ^ 3 - F₀ := D.point_equation h₂
  have key : t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)
      = (x₁ - x₂) * ((x₁ - C.x) ^ 2 + (x₁ - C.x) * (x₂ - C.x) + (x₂ - C.x) ^ 2) := by
    linear_combination hst₁ - hst₂
  have hX₁ : v (x₁ - C.x) ≤ m := depth_le_deviations D _ _ hs₁.le ht₁.le
  have hX₂ : v (x₂ - C.x) ≤ m := depth_le_deviations D _ _ hs₂.le ht₂.le
  have hQ : v ((x₁ - C.x) ^ 2 + (x₁ - C.x) * (x₂ - C.x) + (x₂ - C.x) ^ 2) ≤ m * m := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · rw [Valuation.map_pow, sq]; exact mul_le_mul' hX₁ hX₁
    · rw [Valuation.map_mul]; exact mul_le_mul' hX₁ hX₂
    · rw [Valuation.map_pow, sq]; exact mul_le_mul' hX₂ hX₂
  have hdx : (D.β - D.α) * (x₁ - x₂) = (s₁ - s₂) - (t₁ - t₂) := by ring
  have hD.βD.α : v (D.β - D.α) = 1 := by rw [Valuation.map_sub_swap, D.separated]
  have hvdx : v (x₁ - x₂) = v ((s₁ - s₂) - (t₁ - t₂)) := by
    rw [← hdx, Valuation.map_mul, hD.βD.α, one_mul]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hvdx' : v (x₁ - x₂) = v (t₁ - t₂) := by
      rw [hvdx, Valuation.map_sub_eq_of_lt_right _ hlt]
    have hpos : 0 < v (t₁ - t₂) := lt_of_le_of_lt zero_le hlt
    have hL : v (t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)) = m * v (t₁ - t₂) := by
      rw [Valuation.map_add_eq_of_lt_right, Valuation.map_mul, hs₁]
      rw [Valuation.map_mul, Valuation.map_mul, ht₂, hs₁]
      exact mul_lt_mul_of_pos_left hlt hm_pos
    have hR : v ((x₁ - x₂) * ((x₁ - C.x) ^ 2 + (x₁ - C.x) * (x₂ - C.x) + (x₂ - C.x) ^ 2))
        ≤ v (t₁ - t₂) * (m * m) := by
      rw [Valuation.map_mul, hvdx']; exact mul_le_mul' le_rfl hQ
    rw [← key, hL] at hR
    have : m * v (t₁ - t₂) ≤ (m * m) * v (t₁ - t₂) := by rwa [mul_comm (v (t₁ - t₂))] at hR
    have h1 : m * 1 ≤ m * m := by
      rw [mul_one]; exact le_of_mul_le_mul_right this hpos
    exact (not_le_of_gt hm1) (le_of_mul_le_mul_left h1 hm_pos)
  · have hvdx' : v (x₁ - x₂) = v (s₁ - s₂) := by
      rw [hvdx, Valuation.map_sub_eq_of_lt_left _ hlt]
    have hpos : 0 < v (s₁ - s₂) := lt_of_le_of_lt zero_le hlt
    have hL : v (t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)) = m * v (s₁ - s₂) := by
      rw [Valuation.map_add_eq_of_lt_left, Valuation.map_mul, ht₂]
      rw [Valuation.map_mul, Valuation.map_mul, ht₂, hs₁]
      exact mul_lt_mul_of_pos_left hlt hm_pos
    have hR : v ((x₁ - x₂) * ((x₁ - C.x) ^ 2 + (x₁ - C.x) * (x₂ - C.x) + (x₂ - C.x) ^ 2))
        ≤ v (s₁ - s₂) * (m * m) := by
      rw [Valuation.map_mul, hvdx']; exact mul_le_mul' le_rfl hQ
    rw [← key, hL] at hR
    have : m * v (s₁ - s₂) ≤ (m * m) * v (s₁ - s₂) := by rwa [mul_comm (v (s₁ - s₂))] at hR
    have h1 : m * 1 ≤ m * m := by
      rw [mul_one]; exact le_of_mul_le_mul_right this hpos
    exact (not_le_of_gt hm1) (le_of_mul_le_mul_left h1 hm_pos)
/-- 臨界側の一点の倍点では、有限倍点のX座標は中心へ近づかない。
接線分母非零の下で、分子はv(F₀)、分母の平方はv(F₀)以下になることを使う。 -/
theorem critical_double_not_near [DecidableEq K] (C : CriticalCentre A W) (D : TangentDirections C)
    {x y : K} (h : W.toAffine.Nonsingular x y) (hX : v (x - C.x) < 1)
    (hanti : v (x - C.x) ^ 2 ≤ v (equationDefect W C.x C.y))
    (hΨ : tangentDenominator W x y ≠ 0) :
    ¬ v (W.toAffine.addX x x (W.toAffine.slope x x y y) - C.x) < 1 := by
  obtain ⟨u, hm, hn, hs, hp, _⟩ := critical_deviations C D h.1 hX hanti
  have hFpos : 0 < v (equationDefect W C.x C.y) := (Valuation.pos_iff _).mpr C.defect_ne_zero
  have hFsmall := C.defect_small
  have hfour : v (x - C.x) ^ 4 < v (equationDefect W C.x C.y) := by
    calc v (x - C.x) ^ 4 = (v (x - C.x) ^ 2) ^ 2 := by rw [← pow_mul]
      _ ≤ v (equationDefect W C.x C.y) ^ 2 := pow_le_pow_left₀ zero_le hanti 2
      _ < v (equationDefect W C.x C.y) := by
        rw [sq]
        simpa only [mul_one] using mul_lt_mul_of_pos_left hFsmall hFpos
  have hden : v (tangentDenominator W x y) ^ 2 ≤ v (equationDefect W C.x C.y) := by
    have he : tangentDenominator W x y =
        (y - C.y - D.α * (x - C.x)) + (y - C.y - D.β * (x - C.x)) := by
      dsimp only [tangentDenominator]
      linear_combination (x - C.x) * D.sum_eq + C.derivativeY
    have hv : v (tangentDenominator W x y) ≤ u := by
      rw [he]
      exact (Valuation.map_add _ _ _).trans (by rw [hm, hn, max_self])
    simpa only [sq, hs] using pow_le_pow_left₀ zero_le hv 2
  have heq := congrArg v (doubling_identity C h.1 hΨ)
  rw [map_mul, map_pow, (doubling_numerator_valuation C hX).2 hfour.ne.symm, max_eq_right hfour.le] at heq
  intro hnear
  have hbad := (mul_le_mul' le_rfl hden).trans_lt (mul_lt_mul_of_pos_right hnear hFpos)
  rw [heq, one_mul] at hbad
  exact lt_irrefl _ hbad

/-- 同じ整モデルの臨界側の二つの実際の点の和は滑らかに還元する。
和が無限遠点・非整X・単元X距離の場合と、同一点の接線を全て保持する。 -/
theorem critical_pair_smooth [DecidableEq K] (M : WeierstrassCurve A)
    (C : CriticalCentre A (M.map A.subtype)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (M.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (M.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hanti₁ : v (x₁ - C.x) ^ 2 ≤ v (equationDefect (M.map A.subtype) C.x C.y))
    (hX₂ : v (x₂ - C.x) < 1) (hanti₂ : v (x₂ - C.x) ^ 2 ≤ v (equationDefect (M.map A.subtype) C.x C.y)) :
    HasSmoothReduction M (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) := by
  classical
  obtain ⟨u, hm₁, hn₁, hs, hp, _⟩ := critical_deviations C D h₁.1 hX₁ hanti₁
  obtain ⟨u₂, hm₂, hn₂, hs₂, _, _⟩ := critical_deviations C D h₂.1 hX₂ hanti₂
  have huu : u₂ = u := (pow_left_inj₀ zero_le zero_le two_ne_zero).mp (by simpa only [sq] using hs₂.trans hs.symm)
  have hm₂' := hm₂.trans huu
  have hn₂' := hn₂.trans huu
  have hu1 : u < 1 := by
    by_contra hu
    have hb : (1 : A.ValueGroup) ≤ u * u := by simpa only [one_mul] using mul_le_mul' (not_lt.mp hu) (not_lt.mp hu)
    exact (not_le_of_gt C.defect_small) (hs ▸ hb)
  have hd := equal_deviation_differences C D h₁.1 h₂.1 hu1 hm₁ hn₁ hm₂' hn₂'
  by_cases hz : (y₁ - y₂) - D.α * (x₁ - x₂) = 0
  · have hzβ : (y₁ - y₂) - D.β * (x₁ - x₂) = 0 := by
      apply (Valuation.zero_iff A.valuation).mp
      rw [← hd, hz, _root_.map_zero]
    have hxd : (D.β - D.α) * (x₁ - x₂) = 0 := by linear_combination hz - hzβ
    have hx : x₁ = x₂ := sub_eq_zero.mp ((mul_eq_zero.mp hxd).resolve_left (sub_ne_zero.mpr D.ne.symm))
    have hy : y₁ = y₂ := by rw [hx, sub_self, mul_zero, sub_zero] at hz; exact sub_eq_zero.mp hz
    subst x₂
    subst y₂
    by_cases hΨ : tangentDenominator (M.map A.subtype) x₁ y₁ = 0
    · have hny : y₁ = (M.map A.subtype).toAffine.negY x₁ y₁ := by
        dsimp only [tangentDenominator] at hΨ
        dsimp only [Affine.negY]
        linear_combination hΨ
      rw [Point.add_self_of_Y_eq hny]
      exact hasSmoothReduction_zero M _
    · rw [Point.add_self_of_Y_ne (by
        intro he
        apply hΨ
        dsimp only [tangentDenominator, Affine.negY] at *
        linear_combination he)]
      by_contra hn
      have hv := (not_hasSmoothReduction_some_iff M C _).mp hn
      exact critical_double_not_near C D h₁ hX₁ hanti₁ hΨ hv
  · rcases chord_of_equal_deviation M C D h₁ h₂ hX₁ hX₂ hd hz with h0 | ⟨x₃, y₃, h₃, he, hpole | ⟨hunit, _⟩⟩
    · rw [h0]
      exact hasSmoothReduction_zero M _
    · rw [he]
      exact hasSmoothReduction_of_notMem M h₃ hpole
    · rw [he]
      by_contra hn
      have hv := (not_hasSmoothReduction_some_iff M C h₃).mp hn
      rw [hunit] at hv
      exact lt_irrefl _ hv

end DkMath.Lib.NumberTheory.EllipticCriticalPair
