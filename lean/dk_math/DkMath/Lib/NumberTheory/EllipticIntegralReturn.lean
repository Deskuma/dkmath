/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalPair

#print "file: DkMath.Lib.NumberTheory.EllipticIntegralReturn"

/-!
# NOTE-031-002: 整な滑らかな点を加えたときの中心近傍への復帰

prime-to-residue-characteristic torsionでは全有限倍点の座標が整である。
この整性を使う経路では、先に全点の零成分部分群を構成する必要がない。
滑らかに還元する整な点のX距離は単元であり、中心近傍の点との弦の分母も単元になる。
実際の加法公式を評価して和の近さを直接証明し、その後既存の遷移を逆向きに使う。
非整な滑らかな点との加法はこの定理の範囲に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticIntegralReturn
open WeierstrassCurve Affine Affine.Point EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticAdditionDepth EllipticOppositeDepth EllipticCriticalAddition
open EllipticGoodReductionSeparation EllipticNodalReduction
variable {K : Type*} [Field K] {A : ValuationSubring K} (M : WeierstrassCurve A)
local notation "V" => M.map A.subtype
local notation "v" => A.valuation

/-- 整な滑らかな点に中心近傍の点を加えると、実際の和は有限で再び中心へ近づく。
弦のX分母の単元性を使う直接証明であり、零成分の加法閉性を仮定しない。 -/
theorem integral_smooth_add_near [DecidableEq K] (C : CriticalCentre A (V))
    {x₁ y₁ x₂ y₂ : K} (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hP : HasSmoothReduction M (Point.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A)
    (hX₂ : v (x₂ - C.x) < 1) :
    ∃ (x₃ y₃ : K) (h₃ : (V).toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 := by
  classical
  have hn₁ : ¬ v (x₁ - C.x) < 1 := fun hn => (not_hasSmoothReduction_some_iff M C h₁).mpr hn hP
  have hx₁v : v (x₁ - C.x) = 1 := le_antisymm
    ((A.valuation_le_one_iff _).mpr (A.toSubring.sub_mem hx₁ C.x_mem)) (not_lt.mp hn₁)
  have hx₁0 : x₁ - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp (hx₁v.trans_ne one_ne_zero)
  have hy₁ := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A M _ rfl h₁.1 hx₁
  have hY₂ := y_small_of_x_small M C h₂ hX₂
  have hxne : x₁ ≠ x₂ := by
    intro he
    rw [← he, hx₁v] at hX₂
    exact lt_irrefl _ hX₂
  have hd : v ((x₁ - C.x) - (x₂ - C.x)) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rwa [hx₁v]), hx₁v]
  let t := centreSlope C x₁ y₁
  let l := (V).toAffine.slope x₁ x₂ y₁ y₂
  have ht : v t ≤ 1 := by
    dsimp only [t, centreSlope]
    rw [map_div₀, hx₁v, div_one]
    exact (A.valuation_le_one_iff _).mpr (A.toSubring.sub_mem hy₁ C.y_mem)
  have hl_eq : l - t = (t * (x₂ - C.x) - (y₂ - C.y)) / ((x₁ - C.x) - (x₂ - C.x)) := by
    dsimp only [l, t, centreSlope]
    rw [slope_of_X_ne hxne]
    field_simp [hx₁0, sub_ne_zero.mpr hxne]
    ring
  have hlt : v (l - t) < 1 := by
    rw [hl_eq, map_div₀, hd, div_one]
    apply Valuation.map_sub_lt _ ?_ hY₂
    rw [map_mul]
    exact (mul_le_of_le_one_left' ht).trans_lt hX₂
  have hl : v l ≤ 1 := by
    have he : l = (l - t) + t := by ring
    rw [he]
    exact (Valuation.map_add _ _ _).trans (max_le hlt.le ht)
  have ha₁ : v (V).a₁ ≤ 1 := (A.valuation_le_one_iff _).mpr M.a₁.property
  have hq : v ((l ^ 2 + (V).a₁ * l - ((V).a₂ + 3 * C.x)) -
      (t ^ 2 + (V).a₁ * t - ((V).a₂ + 3 * C.x))) < 1 := by
    rw [show (l ^ 2 + (V).a₁ * l - ((V).a₂ + 3 * C.x)) -
      (t ^ 2 + (V).a₁ * t - ((V).a₂ + 3 * C.x)) = (l - t) * (l + t + (V).a₁) by ring, map_mul]
    have hs : v (l + t + (V).a₁) ≤ 1 := Valuation.map_add_le _ (Valuation.map_add_le _ hl ht) ha₁
    exact (mul_le_of_le_one_right' hs).trans_lt hlt
  have hF : v (equationDefect (V) C.x C.y / (x₁ - C.x) ^ 2) < 1 := by
    rw [map_div₀, map_pow, hx₁v, one_pow, div_one]
    exact C.defect_small
  have hid : (V).toAffine.addX x₁ x₂ l - C.x =
      ((l ^ 2 + (V).a₁ * l - ((V).a₂ + 3 * C.x)) -
        (t ^ 2 + (V).a₁ * t - ((V).a₂ + 3 * C.x))) -
          equationDefect (V) C.x C.y / (x₁ - C.x) ^ 2 - (x₂ - C.x) := by
    have he := centreSlope_quadratic C h₁.1 hx₁0
    change t ^ 2 + (V).a₁ * t - ((V).a₂ + 3 * C.x) = _ at he
    dsimp only [Affine.addX]
    linear_combination he
  refine ⟨_, _, _, Point.add_of_X_ne hxne, ?_⟩
  change v ((V).toAffine.addX x₁ x₂ l - C.x) < 1
  rw [hid]
  exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ hq hF) hX₂
private theorem near_of_squared_product {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {n l f : Γ}
    (he : (n * l) ^ 2 = f) (hsh : f < l ^ 2) : n < 1 := by
  by_contra hn
  have hb : l ^ 2 ≤ (n * l) ^ 2 := pow_le_pow_left₀ zero_le (by simpa only [one_mul] using mul_le_mul' (not_lt.mp hn) (le_refl l)) 2
  exact (not_le_of_gt hsh) (he ▸ hb)
private theorem near_of_product {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {n l r : Γ}
    (he : n * l = r) (hlt : r < l) : n < 1 := by
  by_contra hn
  have hb : l ≤ n * l := by simpa only [one_mul] using mul_le_mul' (not_lt.mp hn) (le_refl l)
  exact (not_le_of_gt hlt) (he ▸ hb)

/-- 整な滑らかな点を加えると、近傍の点の浅い深さと枝、または臨界側という分類を保つ。
復帰の有限点は直接構成し、既存の加法遷移を逆向きに使って分類を確定する。
零成分部分群の閉性・慣性固定・全倍点の性質は入力として仮定しない。 -/
theorem integral_smooth_add_preserves [DecidableEq K] (C : CriticalCentre A (V)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hP : HasSmoothReduction M (Point.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A)
    (hX₂ : v (x₂ - C.x) < 1) :
    ∃ (x₃ y₃ : K) (h₃ : (V).toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 ∧
      (v (equationDefect (V) C.x C.y) < v (x₂ - C.x) ^ 2 →
        v (x₃ - C.x) = v (x₂ - C.x) ∧ v (centreSlope C x₃ y₃ - centreSlope C x₂ y₂) < 1) ∧
      (v (x₂ - C.x) ^ 2 ≤ v (equationDefect (V) C.x C.y) →
        v (x₃ - C.x) ^ 2 ≤ v (equationDefect (V) C.x C.y)) := by
  classical
  obtain ⟨x₃, y₃, h₃, he, hX₃⟩ := integral_smooth_add_near M C h₁ h₂ hP hx₁ hX₂
  have hfar : ∀ {x y : K} (h : (V).toAffine.Nonsingular x y),
      (Point.some x y h : (V).toAffine.Point) = Point.some x₁ y₁ h₁ → ¬ v (x - C.x) < 1 := by
    intro x y h heq hn
    have hs := (not_hasSmoothReduction_some_iff M C h).mpr hn
    exact hs (heq.symm ▸ hP)
  have h₂n : (V).toAffine.Nonsingular x₂ ((V).toAffine.negY x₂ y₂) := (nonsingular_neg ..).mpr h₂
  have hR : (Point.some x₃ y₃ h₃ + Point.some x₂ ((V).toAffine.negY x₂ y₂) h₂n : (V).toAffine.Point) =
      Point.some x₁ y₁ h₁ := by
    rw [← Point.neg_some h₂, ← he, add_neg_cancel_right]
  have hR' : (Point.some x₂ ((V).toAffine.negY x₂ y₂) h₂n + Point.some x₃ y₃ h₃ : (V).toAffine.Point) =
      Point.some x₁ y₁ h₁ := (add_comm _ _).trans hR
  refine ⟨x₃, y₃, h₃, he, hX₃, ?_, ?_⟩
  · intro hsh₂
    have hsh₃ : v (equationDefect (V) C.x C.y) < v (x₃ - C.x) ^ 2 := by
      by_contra hn
      obtain ⟨x, y, h, hsum, hlev, _⟩ := critical_add_shallow C D h₃ h₂n hX₃ (not_lt.mp hn) hX₂ hsh₂
      exact hfar h (hsum.symm.trans hR) (near_of_squared_product hlev hsh₂)
    have hbr : v (centreSlope C x₃ y₃ - centreSlope C x₂ ((V).toAffine.negY x₂ y₂)) = 1 := by
      have ht₃ := (A.valuation_le_one_iff _).mpr (slope_mem_and_branches_of_shallow D h₃.1 hX₃ hsh₃).1
      have ht₂ := (A.valuation_le_one_iff _).mpr (slope_mem_and_branches_of_shallow D h₂n.1 hX₂ hsh₂).1
      have hdist := (Valuation.map_sub _ (centreSlope C x₃ y₃)
        (centreSlope C x₂ ((V).toAffine.negY x₂ y₂))).trans (max_le ht₃ ht₂)
      rcases hdist.lt_or_eq with hb | hb
      · obtain ⟨x, y, h, hsum, hn, _⟩ := same_branch_add C D h₃ h₂n hX₃ hX₂ hsh₃ hsh₂ hb
        exact (hfar h (hsum.symm.trans hR) hn).elim
      · exact hb
    have hdep : v (x₃ - C.x) = v (x₂ - C.x) := by
      rcases lt_trichotomy (v (x₃ - C.x)) (v (x₂ - C.x)) with hlt | heq | hgt
      · obtain ⟨x, y, h, hsum, hlev, _⟩ := opposite_branch_add_of_depth_lt C h₃ h₂n hX₂ hlt hsh₃ hbr
        exact (hfar h (hsum.symm.trans hR) (near_of_product hlev hlt)).elim
      · exact heq
      · have hb : v (centreSlope C x₂ ((V).toAffine.negY x₂ y₂) - centreSlope C x₃ y₃) = 1 :=
          (Valuation.map_sub_swap _ _ _).trans hbr
        obtain ⟨x, y, h, hsum, hlev, _⟩ := opposite_branch_add_of_depth_lt C h₂n h₃ hX₃ hgt hsh₂ hb
        exact (hfar h (hsum.symm.trans hR') (near_of_product hlev hgt)).elim
    refine ⟨hdep, ?_⟩
    have hq₃ := quadratic_small_of_shallow C h₃.1 hX₃ hsh₃
    have hq₂ := quadratic_small_of_shallow C h₂.1 hX₂ hsh₂
    have hsmall := Valuation.map_sub_lt v hq₃ hq₂
    have hid : (centreSlope C x₃ y₃ - centreSlope C x₂ y₂) *
        (centreSlope C x₃ y₃ + centreSlope C x₂ y₂ + (V).a₁) =
        (centreSlope C x₃ y₃ ^ 2 + (V).a₁ * centreSlope C x₃ y₃ - ((V).a₂ + 3 * C.x)) -
        (centreSlope C x₂ y₂ ^ 2 + (V).a₁ * centreSlope C x₂ y₂ - ((V).a₂ + 3 * C.x)) := by ring
    rw [centreSlope_negY C x₂ y₂ (shallow_x_ne C hsh₂)] at hbr
    have hunit : v (centreSlope C x₃ y₃ + centreSlope C x₂ y₂ + (V).a₁) = 1 := by
      convert hbr using 1
      congr 1
      ring
    rw [← hid, map_mul, hunit, mul_one] at hsmall
    exact hsmall
  · intro hanti₂
    by_contra hn
    obtain ⟨x, y, h, hsum, hlev, _⟩ := critical_add_shallow C D h₂n h₃ hX₂ hanti₂ hX₃ (not_le.mp hn)
    exact hfar h (hsum.symm.trans hR') (near_of_squared_product hlev (not_le.mp hn))

/-- 同じ一般ファイバーのモデル一致を保って、整な滑らかな点との加法の復帰則を輸送する。 -/
theorem integral_smooth_add_preserves_of_model [DecidableEq K]
    (E : WeierstrassCurve K) (hmodel : M.map A.subtype = E) (C : CriticalCentre A E) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP : HasSmoothReduction M (Point.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A)
    (hX₂ : v (x₂ - C.x) < 1) :
    ∃ (x₃ y₃ : K) (h₃ : E.toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 ∧
      (v (equationDefect E C.x C.y) < v (x₂ - C.x) ^ 2 →
        v (x₃ - C.x) = v (x₂ - C.x) ∧ v (centreSlope C x₃ y₃ - centreSlope C x₂ y₂) < 1) ∧
      (v (x₂ - C.x) ^ 2 ≤ v (equationDefect E C.x C.y) →
        v (x₃ - C.x) ^ 2 ≤ v (equationDefect E C.x C.y)) := by
  subst E
  exact integral_smooth_add_preserves M C D h₁ h₂ hP hx₁ hX₂

end DkMath.Lib.NumberTheory.EllipticIntegralReturn
