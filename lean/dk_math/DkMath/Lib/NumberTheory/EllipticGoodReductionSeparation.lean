/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Chord estimates adapted from S_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean,
blob 38bdee599f8b536cb30402a8d1dbef001a3d89da.
Modified: extract pointwise smooth-reduction separation; reuse DkMath coordinate integrality;
avoid the full formal-group and zero-component construction.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality

#print "file: DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation"

/-!
# NOTE-031-002B: 同じ剰余点へ重なる異なる点の差には極がある

良い剰余曲線では、有限点の二つの偏微分が同時に消えない。
互いに逆の剰余座標を持つ二点を足すと、傾きが付値環を外れ、
和のx座標も付値環を外れる。接線・割線の両方と、剰余標数2も扱う。

次の章ではP−Qへ適用する。P,Qと差点が全てprime-to-q torsionなら、
前章の座標整性に反するので、同じ剰余座標のtorsion点は等しくなる。
この章自体は還元写像の加法性を仮定せず、実際の点の加法公式を使う。

031-002C1では一点の滑らかな還元へ一般化する。剰余判別式が零でも、
当該点が非特異なら同じ証明が通る。従来の良還元APIはその特殊化として保つ。
-/
namespace DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L]
private theorem mul_mem_nonunits (A : ValuationSubring L) {a x : L}
    (ha : a ∈ A) (hx : x ∈ A.nonunits) : a * x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

private theorem add_notMem (A : ValuationSubring L) {x a : L} (hx : x ∉ A) (ha : a ∈ A) : x + a ∉ A := fun h =>
  hx (by simpa using A.toSubring.sub_mem h ha)


private theorem mul_notMem (A : ValuationSubring L) {x y : L} (hx : x ∉ A) (hy : y ∉ A) : x * y ∉ A := fun h => by
  rcases A.mem_or_inv_mem x with hx' | hx'
  · exact hx hx'
  · have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
    exact hy (by simpa [inv_mul_cancel_left₀ hx0] using A.toSubring.mul_mem hx' h)


private theorem div_notMem (A : ValuationSubring L) {a b : L} (ha' : a ∉ A.nonunits) (hb : b ∈ A.nonunits) (hb0 : b ≠ 0) :
    a / b ∉ A := fun h => by
  refine ha' ?_
  rw [show a = a / b * b from (div_mul_cancel₀ a hb0).symm]
  exact mul_mem_nonunits A h hb


private theorem coe_mem_nonunits_iff_residue_eq_zero (A : ValuationSubring L) (e : A) :
    (e : L) ∈ A.nonunits ↔ residue A e = 0 := by
  rw [ValuationSubring.coe_mem_nonunits_iff, residue_eq_zero_iff]


/-- 整な有限座標の曲線方程式は、同じモデルの剰余曲線の方程式へ写る。 -/
theorem equation_residue {A : ValuationSubring L} (W : WeierstrassCurve A) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Equation (residue A x) (residue A y) := by
  have hA : W.toAffine.Equation x y := (W.toAffine.map_equation A.subtype_injective x y).mp h
  exact hA.map (residue A)

/-- 剰余判別式が非零なら、整な有限座標の還元は実際に非特異である。 -/
theorem nonsingular_residue {A : ValuationSubring L} (W : WeierstrassCurve A)
    (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (equation_residue W h)

/-- 二点の曲線方程式の差を、割線に必要な二つの積へ因数分解する。 -/
theorem sub_mul_sub_negY {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (h₁ : V.Equation x₁ y₁) (h₂ : V.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ - V.negY x₂ y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) := by
  rw [Affine.equation_iff] at h₁ h₂
  rw [Affine.negY]
  linear_combination h₁ - h₂

variable {A : ValuationSubring L} (W : WeierstrassCurve A)

/-- 指定された有限座標の還元だけが非特異である条件。
曲線全体の判別式の単元性は要求しない。整性の証明項による違いは生じない。 -/
def SmoothCoordinates (x y : L) : Prop :=
  ∀ (hx : x ∈ A) (hy : y ∈ A),
    (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)

/-- 点の滑らかな還元の座標的条件。有限座標が整なら、その剰余点の非特異性を要求する。
無限遠点および非整なx座標の点はこの条件を満たす。後者を除外して零成分を縮めない。
V上の点をWのモデルで調べるため、幾何学への適用定理ではW.map A.subtype = Vも要求する。
本定義だけで加法閉性や零成分部分加群を構成したとはしない。 -/
def HasSmoothReduction {V : WeierstrassCurve L} (P : V.toAffine.Point) : Prop :=
  ∀ x y (h : V.toAffine.Nonsingular x y), P = .some x y h → SmoothCoordinates W x y

/-- 無限遠点は滑らかな還元条件を満たす。便宜的な有限座標は割り当てない。 -/
theorem hasSmoothReduction_zero (V : WeierstrassCurve L) : HasSmoothReduction W (0 : V.toAffine.Point) :=
  fun _ _ h heq => absurd heq (Ne.symm (Affine.Point.some_ne_zero h))

/-- 有限点の滑らかな還元条件は、その座標での条件と同値である。 -/
theorem hasSmoothReduction_some_iff {V : WeierstrassCurve L} {x y : L}
    (h : V.toAffine.Nonsingular x y) :
    HasSmoothReduction W (.some x y h) ↔ SmoothCoordinates W x y := by
  refine ⟨fun hP => hP x y h rfl, fun hs x' y' h' heq => ?_⟩
  obtain ⟨rfl, rfl⟩ := Affine.Point.some.inj heq
  exact hs

/-- 非整なx座標の点も滑らかな還元条件に含める。
prime-to-q torsionでは別途証明した座標整性により、この枝は起きない。 -/
theorem hasSmoothReduction_of_notMem {V : WeierstrassCurve L} {x y : L}
    (h : V.toAffine.Nonsingular x y) (hx : x ∉ A) : HasSmoothReduction W (.some x y h) :=
  (hasSmoothReduction_some_iff W h).mpr fun hx' _ => absurd hx' hx

/-- 良い剰余曲線では全点が滑らかな還元条件を満たす。 -/
theorem hasSmoothReduction_of_good (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : HasSmoothReduction W P :=
  fun _ _ h _ _ _ => nonsingular_residue W hΔ h.1

/-- Y方向の偏微分が消える滑らかな剰余点では、X方向の偏微分は単元となる。
必要なのは当該一点の非特異性であり、他の剰余点の特異性は妨げない。 -/
theorem notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth
    {x y : L} (hs : SmoothCoordinates W x y) (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A)
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits := by
  have hy : y ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W (W.map A.subtype) rfl h hx
  set eX : A := 3 * ⟨x, hx⟩ ^ 2 + 2 * W.a₂ * ⟨x, hx⟩ + W.a₄ - W.a₁ * ⟨y, hy⟩ with heX
  set eY : A := ⟨y, hy⟩ - W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ with heY
  have hcoeX : (eX : L) = 3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x +
      (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y := by
    push_cast [heX]
    rfl
  have hcoeY : (eY : L) = y - (W.map A.subtype).toAffine.negY x y := by
    have h1 : ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
      (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    rw [heY]
    push_cast
    rw [h1]
  have hns := hs hx hy
  rw [Affine.nonsingular_iff] at hns
  have hY0 : residue A eY = 0 := by
    rw [← coe_mem_nonunits_iff_residue_eq_zero A, hcoeY]
    exact hY
  have hX0 : residue A eX ≠ 0 := by
    rcases hns.2 with hX | hY'
    · intro h0
      apply hX
      rw [heX] at h0
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h0
      change residue A W.a₁ * residue A ⟨y, hy⟩ = 3 * residue A ⟨x, hx⟩ ^ 2 +
        2 * residue A W.a₂ * residue A ⟨x, hx⟩ + residue A W.a₄
      linear_combination -h0
    · exact absurd (by
        change residue A ⟨y, hy⟩ = -residue A ⟨y, hy⟩ - residue A W.a₁ * residue A ⟨x, hx⟩ -
          residue A W.a₃
        rw [heY] at hY0
        simp only [Affine.negY, map_sub, map_neg, map_mul] at hY0
        linear_combination hY0) hY'
  rw [← hcoeX, coe_mem_nonunits_iff_residue_eq_zero A]
  exact hX0

/-- 良還元は、偏微分の単元性に必要な一点の滑らかさを供給する。 -/
theorem notMem_nonunits_of_sub_negY_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x y : L} (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A)
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits :=
  notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth W
    (fun _ _ => nonsingular_residue W hΔ h) h hx hY

section Slope

variable [DecidableEq L]


/-- 逆の剰余座標を持つ二点の和が非零なら、その接線または割線の傾きは付値環を外れる。 -/
theorem slope_notMem_of_sub_mem_nonunits_of_smooth
    {x₁ x₂ y₁ y₂ : L} (hs : SmoothCoordinates W x₁ y₁) (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A := by
  have hy₁ : y₁ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W (W.map A.subtype) rfl h₁ hx₁
  have hy₂ : y₂ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W (W.map A.subtype) rfl h₂ hx₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have hnegY : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := by
    rw [Affine.negY]
    exact A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy₂)
      (A.toSubring.mul_mem ha₁ hx₂)) ha₃
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hPQ ⟨hx, h⟩
    have hy12 : y₁ = y₂ := (Affine.Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    rw [Affine.slope_of_Y_ne hx hy]
    have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
      rwa [← hx, ← hy12] at hyy
    have hden0 : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hy (by rw [← hx, ← hy12]; exact hcon)
    have hnum := notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth W hs h₁ hx₁ hden
    exact div_notMem A hnum hden hden0
  · by_cases hyy' : y₁ - y₂ ∈ A.nonunits
    · rw [Affine.slope_of_X_ne hx]
      have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
        have key : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) + (y₁ - y₂) +
              (W.map A.subtype).toAffine.a₁ * (x₁ - x₂) := by
          simp only [Affine.negY]
          ring
        rw [key]
        exact add_mem (add_mem hyy hyy') (mul_mem_nonunits A ha₁ hxx)
      have hnum := notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth W hs h₁ hx₁ hden
      set N : L := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ with hN
      have hNunit : N ∉ A.nonunits := by
        intro hmem
        apply hnum
        have key : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
            (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ =
            N - (x₁ + x₁ + x₂ + (W.map A.subtype).toAffine.a₂) * -(x₁ - x₂) := by
          rw [hN]; ring
        rw [key]
        exact sub_mem hmem (mul_mem_nonunits A
          (add_mem (add_mem (add_mem hx₁ hx₁) hx₂) ha₂) (neg_mem hxx))
      have hd0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 := by
        intro hd
        apply hNunit
        rw [hN]
        have hid := sub_mul_sub_negY h₁ h₂
        rw [hd, mul_zero] at hid
        rcases mul_eq_zero.mp hid.symm with h | h
        · exact absurd (sub_eq_zero.mp h) hx
        · rw [h]
          exact zero_mem _
      have hslope : (y₁ - y₂) / (x₁ - x₂) = N / (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr hx) hd0, hN]
        linear_combination sub_mul_sub_negY h₁ h₂
      rw [hslope]
      exact div_notMem A hNunit hyy hd0
    · rw [Affine.slope_of_X_ne hx]
      exact div_notMem A hyy' hxx (sub_ne_zero.mpr hx)


/-- 逆の剰余座標を持つ二点の非零な和はx座標に極を持つ。傾きの二次項が支配する。 -/
theorem addX_notMem_of_sub_mem_nonunits_of_smooth
    {x₁ x₂ y₁ y₂ : L} (hs : SmoothCoordinates W x₁ y₁) (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hℓ := slope_notMem_of_sub_mem_nonunits_of_smooth W hs h₁ h₂ hx₁ hx₂ hPQ hxx hyy
  set ℓ : L := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  rw [show (W.map A.subtype).toAffine.addX x₁ x₂ ℓ =
    ℓ * (ℓ + (W.map A.subtype).toAffine.a₁) +
      (-(W.map A.subtype).toAffine.a₂ - x₁ - x₂) from by rw [Affine.addX]; ring]
  exact add_notMem A (mul_notMem A hℓ (by simpa [add_comm] using add_notMem A hℓ ha₁))
    (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₂) hx₁) hx₂)

/-- 良還元から一点の滑らかさを供給する、従来の傾きの入口。 -/
theorem slope_notMem_of_sub_mem_nonunits
    (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A :=
  slope_notMem_of_sub_mem_nonunits_of_smooth W (fun _ _ => nonsingular_residue W hΔ h₁)
    h₁ h₂ hx₁ hx₂ hPQ hxx hyy

/-- 良還元から一点の滑らかさを供給する、従来の和の極の入口。 -/
theorem addX_notMem_of_sub_mem_nonunits
    (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A :=
  addX_notMem_of_sub_mem_nonunits_of_smooth W (fun _ _ => nonsingular_residue W hΔ h₁)
    h₁ h₂ hx₁ hx₂ hPQ hxx hyy

end Slope
end DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
