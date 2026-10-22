/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Node-chord comparison informed by S_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq,
blob 829600493f3eabf22160657058a3a83fba5ec103, NodeChord.node_chord_core, ch_core and ch_pm.
Modified: arbitrary field/integral model; reuse DkMath centre, directions and smooth-reduction
criterion; reconstruct branch transfer using separated roots, preserving the actual point group.
-/

import DkMath.Lib.NumberTheory.EllipticShallowSlope
import DkMath.Lib.NumberTheory.EllipticNodalReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

#print "file: DkMath.Lib.NumberTheory.EllipticBranchComparison"

/-!
# NOTE-031-002C5: 同じ深さでの枝と実際の点の和差

同じ枝の二点は差を、異なる枝の二点は和を取ると滑らかな還元へ移る。
結果が整な有限点ならv(x₁−x₂)=v(x₁−x₀)も確定する。
無限遠点・非整座標・同じX座標を捨てず、実際のAffine.Pointの演算で場合分けする。
中心Cと方向Dを取り直さず、同じ整モデルを通して還元条件へ接続する。
この比較はtorsionの深さの漸化式や全点の慣性固定をまだ主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticBranchComparison
open WeierstrassCurve Affine Affine.Point
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
open EllipticGoodReductionSeparation EllipticNodalReduction
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} (W : WeierstrassCurve A)
local notation "V" => W.map A.subtype
local notation "v" => A.valuation

private theorem node_chord_core (C : CriticalCentre A V) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hΔ : v ((y₁ - y₂) - D.α * (x₁ - x₂)) = v ((y₁ - y₂) - D.β * (x₁ - x₂)))
    (hne : (y₁ - y₂) - D.α * (x₁ - x₂) ≠ 0) :
    (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (V).toAffine.Point) = 0 ∨
      ∃ (x₃ y₃ : L) (h₃ : (V).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (V).toAffine.Point)
            = Point.some x₃ y₃ h₃ ∧
          (x₃ ∉ A ∨ (v (x₃ - C.x) = 1 ∧
            v (x₁ - x₂) = v ((y₁ - y₂) - D.α * (x₁ - x₂)))) := by
  classical
  set Ds := (y₁ - y₂) - D.α * (x₁ - x₂) with hDs
  set Dt := (y₁ - y₂) - D.β * (x₁ - x₂) with hDt
  have hst : Ds - Dt = (D.β - D.α) * (x₁ - x₂) := by rw [hDs, hDt]; ring
  by_cases hx : x₁ = x₂
  · rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with hy | hy
    · exfalso
      apply hne
      rw [hDs, hy, hx]
      ring
    · exact Or.inl (add_of_Y_eq hx hy)
  · right
    rw [add_of_X_ne hx]
    refine ⟨_, _, _, rfl, ?_⟩
    set ell := (V).toAffine.slope x₁ x₂ y₁ y₂ with hL
    have hD0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hLeq : ell = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx
    have hLα : ell - D.α = Ds / (x₁ - x₂) := by
      rw [eq_div_iff hD0, sub_mul, hLeq, div_mul_cancel₀ _ hD0]
    have hLβ : ell - D.β = Dt / (x₁ - x₂) := by
      rw [eq_div_iff hD0, sub_mul, hLeq, div_mul_cancel₀ _ hD0]
    have hX₃ : (V).toAffine.addX x₁ x₂ ell - C.x = (ell - D.α) * (ell - D.β) - ((x₁ - C.x) + (x₂ - C.x)) := by
      change _ ^ 2 + (V).a₁ * _ - (V).a₂ - x₁ - x₂ - C.x = _
      linear_combination ell * D.sum_eq - D.product_eq
    have ha₁ : v (V).a₁ ≤ 1 := (A.valuation_le_one_iff _).mpr W.a₁.property
    have ha₂ : v (V).a₂ ≤ 1 := (A.valuation_le_one_iff _).mpr W.a₂.property
    have hx₁A : x₁ ∈ A := by
      have ha : x₁ - C.x + C.x ∈ A := A.toSubring.add_mem ((A.valuation_le_one_iff _).mp hX₁.le) C.x_mem
      simpa only [sub_add_cancel] using ha
    have hx₂A : x₂ ∈ A := by
      have ha : x₂ - C.x + C.x ∈ A := A.toSubring.add_mem ((A.valuation_le_one_iff _).mp hX₂.le) C.x_mem
      simpa only [sub_add_cancel] using ha
    have hvD_pos : 0 < v (x₁ - x₂) := (Valuation.pos_iff _).mpr hD0
    have hvD_le : v (x₁ - x₂) ≤ v Ds := by
      have h := Valuation.map_sub (v) Ds Dt
      rw [hst, map_mul, Valuation.map_sub_swap, D.separated, one_mul, ← hΔ, max_self] at h
      exact h
    -- 分母より偏差が大きければ弦傾きは非整。等しければ両方向との差が単元になる。
    rcases hvD_le.lt_or_eq with hlt | heq
    · left
      have hvLα : 1 < v (ell - D.α) := by
        rw [hLα, map_div₀, one_lt_div₀ hvD_pos]; exact hlt
      have hvL : 1 < v ell := by
        have hαv : v D.α ≤ 1 := (A.valuation_le_one_iff D.α).mpr D.α_mem
        have : ell = (ell - D.α) + D.α := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hαv hvLα)]
        exact hvLα
      have hvL0 : v ell ≠ 0 := ne_of_gt (lt_trans zero_lt_one hvL)
      have hvL2 : v ell < v (ell ^ 2) := by
        rw [map_pow, sq]
        calc v ell = v ell * 1 := (mul_one _).symm
          _ < v ell * v ell := mul_lt_mul_of_pos_left hvL (zero_lt_iff.mpr hvL0)
      have h1L2 : 1 < v (ell ^ 2) := hvL.trans hvL2
      have t1 : v ((V).a₁ * ell) < v (ell ^ 2) := by
        rw [map_mul]
        calc v (V).a₁ * v ell ≤ 1 * v ell := mul_le_mul' ha₁ le_rfl
          _ = v ell := one_mul _
          _ < v (ell ^ 2) := hvL2
      have e1 : v (ell ^ 2 + (V).a₁ * ell) = v (ell ^ 2) :=
        Valuation.map_add_eq_of_lt_left _ t1
      have e2 : v (ell ^ 2 + (V).a₁ * ell - (V).a₂)
          = v (ell ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ (by rw [e1]; exact lt_of_le_of_lt ha₂ h1L2), e1]
      have hx₁lt : v x₁ < v (ell ^ 2 + (V).a₁ * ell - (V).a₂) := by
        rw [e2]; exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr hx₁A) h1L2
      have e3 : v (ell ^ 2 + (V).a₁ * ell - (V).a₂ - x₁)
          = v (ell ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ hx₁lt, e2]
      have hx₂lt : v x₂
          < v (ell ^ 2 + (V).a₁ * ell - (V).a₂ - x₁) := by
        rw [e3]; exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr hx₂A) h1L2
      have e4 : v (ell ^ 2 + (V).a₁ * ell - (V).a₂ - x₁ - x₂)
          = v (ell ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ hx₂lt, e3]
      intro hx₃A
      have hle : v ((V).toAffine.addX x₁ x₂ ell) ≤ 1 := (A.valuation_le_one_iff _).mpr hx₃A
      change v (ell ^ 2 + (V).a₁ * ell - (V).a₂ - x₁ - x₂) ≤ 1 at hle
      rw [e4] at hle
      exact absurd (h1L2.trans_le hle) (lt_irrefl 1)
    · right
      have hvD0 : v (x₁ - x₂) ≠ 0 := ne_of_gt hvD_pos
      have hvLα : v (ell - D.α) = 1 := by rw [hLα, map_div₀, ← heq, div_self hvD0]
      have hvLβ : v (ell - D.β) = 1 := by rw [hLβ, map_div₀, ← hΔ, ← heq, div_self hvD0]
      have hvsum : v ((x₁ - C.x) + (x₂ - C.x)) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hX₁ hX₂)
      -- 加法公式の主項は単元、二点の中心からのX差の和は小さい。
      have hvX₃ : v ((V).toAffine.addX x₁ x₂ ell - C.x) = 1 := by
        rw [hX₃, Valuation.map_sub_eq_of_lt_left _
          (by rw [map_mul, hvLα, hvLβ, one_mul]; exact hvsum), map_mul, hvLα, hvLβ, one_mul]
      exact ⟨hvX₃, heq⟩

/-- 接線方向の名前を交換する。同じ中心・同じ二根のままであり、新しい根を選ばない。 -/
def swapDirections {C : CriticalCentre A (V)} (D : TangentDirections C) : TangentDirections C where
  α := D.β
  β := D.α
  α_mem := D.β_mem
  β_mem := D.α_mem
  sum_eq := (add_comm _ _).trans D.sum_eq
  product_eq := (mul_comm _ _).trans D.product_eq
  separated := (Valuation.map_sub_swap _ _ _).trans D.separated

omit [DecidableEq L] in
/-- 中心傾きの方向差をX差で掛けると、割り算のない線形偏差になる。
この式は分母非零の下でのみ用いる。 -/
theorem linear_deviation (C : CriticalCentre A (V)) (x y γ : L) (hx : x - C.x ≠ 0) :
    (y - C.y) - γ * (x - C.x) = (centreSlope C x y - γ) * (x - C.x) := by
  rw [sub_mul, centreSlope, div_mul_cancel₀ _ hx]

private theorem sub_on_first_branch (C : CriticalCentre A (V)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x)) (hx₁ : x₁ - C.x ≠ 0)
    (hα₁ : v (centreSlope C x₁ y₁ - D.α) < 1)
    (hα₂ : v (centreSlope C x₂ y₂ - D.α) < 1) :
    HasSmoothReduction W (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : L} (h₃ : (V).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (V).toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - C.x)) := by
  classical
  have he0 : v (x₁ - C.x) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₁
  have hx₂ : x₂ - C.x ≠ 0 := (Valuation.ne_zero_iff _).mp (hlev ▸ he0)
  have key : ∀ {x y : L}, x - C.x ≠ 0 → v (centreSlope C x y - D.α) < 1 →
      v ((y - C.y) - D.α * (x - C.x)) < v (x - C.x) ∧
        v ((y - C.y) - D.β * (x - C.x)) = v (x - C.x) := by
    intro x y hx ht
    have hβ := DkMath.Lib.Algebra.ValuationSeparatedRoots.right_eq_one_of_near_left v D.separated ht
    rw [linear_deviation W C x y D.α hx, linear_deviation W C x y D.β hx, map_mul, map_mul, hβ, one_mul]
    exact ⟨by simpa only [one_mul] using mul_lt_mul_of_pos_right ht ((Valuation.pos_iff _).mpr hx), rfl⟩
  obtain ⟨hm₁, hn₁⟩ := key hx₁ hα₁
  obtain ⟨hm₂, hn₂⟩ := key hx₂ hα₂
  have h₂' : (V).toAffine.Nonsingular x₂ ((V).toAffine.negY x₂ y₂) := (nonsingular_neg ..).mpr h₂
  have hDs : (y₁ - (V).toAffine.negY x₂ y₂) - D.α * (x₁ - x₂) =
      ((y₁ - C.y) - D.α * (x₁ - C.x)) + ((y₂ - C.y) - D.β * (x₂ - C.x)) := by
    change (y₁ - (-y₂ - (V).a₁ * x₂ - (V).a₃)) - _ = _
    linear_combination (x₂ - C.x) * D.sum_eq + C.derivativeY
  have hDt : (y₁ - (V).toAffine.negY x₂ y₂) - D.β * (x₁ - x₂) =
      ((y₁ - C.y) - D.β * (x₁ - C.x)) + ((y₂ - C.y) - D.α * (x₂ - C.x)) := by
    change (y₁ - (-y₂ - (V).a₁ * x₂ - (V).a₃)) - _ = _
    linear_combination (x₂ - C.x) * D.sum_eq + C.derivativeY
  have hvDs : v ((y₁ - (V).toAffine.negY x₂ y₂) - D.α * (x₁ - x₂)) = v (x₁ - C.x) := by
    rw [hDs, Valuation.map_add_eq_of_lt_right _ (by rw [hn₂, ← hlev]; exact hm₁), hn₂, ← hlev]
  have hvDt : v ((y₁ - (V).toAffine.negY x₂ y₂) - D.β * (x₁ - x₂)) = v (x₁ - C.x) := by
    rw [hDt, Valuation.map_add_eq_of_lt_left _ (by rw [hn₁, hlev]; exact hm₂), hn₁]
  have hΔ : v ((y₁ - (V).toAffine.negY x₂ y₂) - D.α * (x₁ - x₂)) =
      v ((y₁ - (V).toAffine.negY x₂ y₂) - D.β * (x₁ - x₂)) := hvDs.trans hvDt.symm
  have hne : (y₁ - (V).toAffine.negY x₂ y₂) - D.α * (x₁ - x₂) ≠ 0 := by
    intro h0
    rw [h0, _root_.map_zero] at hvDs
    exact he0 hvDs.symm
  have hsub : (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (V).toAffine.Point) =
      .some x₁ y₁ h₁ + Point.some x₂ ((V).toAffine.negY x₂ y₂) h₂' := by
    rw [sub_eq_add_neg, neg_some]
  rcases node_chord_core W C D h₁ h₂' hX₁ hX₂ hΔ hne with h0 | ⟨x₃, y₃, h₃, h3eq, hpole | ⟨hunit, hsharp⟩⟩
  · refine ⟨?_, ?_⟩
    · rw [hsub, h0]
      exact hasSmoothReduction_zero W _
    · intro x₃ y₃ h₃ h _
      exact absurd (h.symm.trans (hsub.trans h0)) (some_ne_zero h₃)
  · refine ⟨?_, ?_⟩
    · rw [hsub, h3eq]
      exact hasSmoothReduction_of_notMem W h₃ hpole
    · intro x₃' y₃' h₃' h hx₃'
      have hxx := (Point.some.inj ((hsub.trans h3eq).symm.trans h)).1
      exact absurd (hxx ▸ hx₃') hpole
  · refine ⟨?_, fun _ _ _ => hsharp.trans hvDs⟩
    rw [hsub, h3eq]
    by_contra hn
    have hv := (not_hasSmoothReduction_some_iff W C h₃).mp hn
    rw [hunit] at hv
    exact lt_irrefl _ hv

omit [DecidableEq L] in
/-- 同じ深さの浅い二点の中心傾きの差は、小さいか単元である。
両傾きの整性から1以下を得るため、この二択は全ての場合を尽くす。
和差の定理の枝条件を仮定する前に、実際の点から二択を供給できる。 -/
theorem branch_distance_dichotomy (C : CriticalCentre A (V)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L} (h₁ : (V).toAffine.Equation x₁ y₁) (h₂ : (V).toAffine.Equation x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x))
    (hsh : v (equationDefect (V) C.x C.y) < v (x₁ - C.x) ^ 2) :
    v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1 ∨
      v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1 := by
  have ht₁ := (slope_mem_and_branches_of_shallow D h₁ hX₁ hsh).1
  have ht₂ := (slope_mem_and_branches_of_shallow D h₂ hX₂ (hlev ▸ hsh)).1
  have hv₁ := (A.valuation_le_one_iff _).mpr ht₁
  have hv₂ := (A.valuation_le_one_iff _).mpr ht₂
  exact ((Valuation.map_sub _ _ _).trans (max_le hv₁ hv₂)).lt_or_eq

/-- 同じ深さの浅い二点が同じ枝にあると、実際の点の差は滑らかに還元する。
枝の名前は指定しない。さらに差が整な有限点なら、元のX差の深さも正確に決まる。
差が無限遠点または非整なら後半の条件は成立せず、便宜的な座標を割り当てない。 -/
theorem sub_of_same_branch (C : CriticalCentre A (V)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x))
    (hsh : v (equationDefect (V) C.x C.y) < v (x₁ - C.x) ^ 2)
    (hbr : v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1) :
    HasSmoothReduction W (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : L} (h₃ : (V).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (V).toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - C.x)) := by
  have transfer : ∀ γ : L, v (centreSlope C x₁ y₁ - γ) < 1 → v (centreSlope C x₂ y₂ - γ) < 1 := by
    intro γ ht
    have he : centreSlope C x₂ y₂ - γ = (centreSlope C x₁ y₁ - γ) -
        (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) := by ring
    rw [he]
    exact Valuation.map_sub_lt _ ht hbr
  rcases (slope_mem_and_branches_of_shallow D h₁.1 hX₁ hsh).2.2 with hα | hβ
  · exact sub_on_first_branch W C D h₁ h₂ hX₁ hX₂ hlev (shallow_x_ne C hsh) hα.1 (transfer _ hα.1)
  · exact sub_on_first_branch W C (swapDirections W D) h₁ h₂ hX₁ hX₂ hlev (shallow_x_ne C hsh)
      hβ.2 (transfer _ hβ.2)

/-- 同じ深さの浅い二点が異なる枝にあると、実際の点の和は滑らかに還元する。
二点目を負号へ移すと同じ枝になり、差の定理が適用できる。
和が整な有限点の場合のX差の深さも保持する。 -/
theorem add_of_opposite_branch (C : CriticalCentre A (V)) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : (V).toAffine.Nonsingular x₁ y₁) (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x))
    (hsh : v (equationDefect (V) C.x C.y) < v (x₁ - C.x) ^ 2)
    (hbr : v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1) :
    HasSmoothReduction W (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : L} (h₃ : (V).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (V).toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - C.x)) := by
  classical
  have hsh₂ : v (equationDefect (V) C.x C.y) < v (x₂ - C.x) ^ 2 := hlev ▸ hsh
  have hx₂ := shallow_x_ne C hsh₂
  have h₂' : (V).toAffine.Nonsingular x₂ ((V).toAffine.negY x₂ y₂) := (nonsingular_neg ..).mpr h₂
  have hbranches₁ := (slope_mem_and_branches_of_shallow D h₁.1 hX₁ hsh).2.2
  have hbranches₂ := (slope_mem_and_branches_of_shallow D h₂.1 hX₂ hsh₂).2.2
  have near_same : ∀ γ : L, v (centreSlope C x₁ y₁ - γ) < 1 →
      v (centreSlope C x₂ y₂ - γ) < 1 → False := by
    intro γ ht₁ ht₂
    have he : centreSlope C x₁ y₁ - centreSlope C x₂ y₂ =
        (centreSlope C x₁ y₁ - γ) - (centreSlope C x₂ y₂ - γ) := by ring
    have hv := Valuation.map_sub_lt v ht₁ ht₂
    rw [← he, hbr] at hv
    exact lt_irrefl _ hv
  have distances := negY_branch_distances D x₂ y₂ hx₂
  have hsub : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (V).toAffine.Point) =
      .some x₁ y₁ h₁ - Point.some x₂ ((V).toAffine.negY x₂ y₂) h₂' := by
    rw [sub_eq_add_neg, neg_some]
    congr 2
    exact (negY_negY x₂ y₂).symm
  rw [hsub]
  rcases hbranches₁ with hα₁ | hβ₁
  · have hβ₂ : v (centreSlope C x₂ y₂ - D.β) < 1 := by
      rcases hbranches₂ with hα₂ | hβ₂
      · exact (near_same _ hα₁.1 hα₂.1).elim
      · exact hβ₂.2
    exact sub_on_first_branch W C D h₁ h₂' hX₁ hX₂ hlev (shallow_x_ne C hsh) hα₁.1 (distances.1 ▸ hβ₂)
  · have hα₂ : v (centreSlope C x₂ y₂ - D.α) < 1 := by
      rcases hbranches₂ with hα₂ | hβ₂
      · exact hα₂.1
      · exact (near_same _ hβ₁.2 hβ₂.2).elim
    exact sub_on_first_branch W C (swapDirections W D) h₁ h₂' hX₁ hX₂ hlev (shallow_x_ne C hsh)
      hβ₁.2 (distances.2 ▸ hα₂)

/-- 同じ一般ファイバーのモデル一致を明示し、中心・方向・点と全ての深さの入力を保持して輸送する。 -/
theorem sub_of_same_branch_of_model (E : WeierstrassCurve L) (hmodel : W.map A.subtype = E)
    (C : CriticalCentre A E) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x))
    (hsh : v (equationDefect E C.x C.y) < v (x₁ - C.x) ^ 2)
    (hbr : v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1) :
    HasSmoothReduction W (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : L} (h₃ : E.toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : E.toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - C.x)) := by
  subst E
  exact sub_of_same_branch W C D h₁ h₂ hX₁ hX₂ hlev hsh hbr

/-- 同じ一般ファイバーのモデル一致を明示し、中心・方向・点と全ての深さの入力を保持して輸送する。 -/
theorem add_of_opposite_branch_of_model (E : WeierstrassCurve L) (hmodel : W.map A.subtype = E)
    (C : CriticalCentre A E) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L}
    (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - C.x) < 1) (hX₂ : v (x₂ - C.x) < 1)
    (hlev : v (x₁ - C.x) = v (x₂ - C.x))
    (hsh : v (equationDefect E C.x C.y) < v (x₁ - C.x) ^ 2)
    (hbr : v (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1) :
    HasSmoothReduction W (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : L} (h₃ : E.toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : E.toAffine.Point) = Point.some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - C.x)) := by
  subst E
  exact add_of_opposite_branch W C D h₁ h₂ hX₁ hX₂ hlev hsh hbr

end DkMath.Lib.NumberTheory.EllipticBranchComparison
