/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre.lean,
blob 7f417364bbc9f0369ceaec5cda32107156ecb069.
Modified: arbitrary valuation-ring model, existing CriticalCentre and HasSmoothReduction;
reuse DkMath coordinate integrality and residue singularity; separate nodal geometry
from zero-component subgroup construction and inertia fixedness.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalCentre
import DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation

#print "file: DkMath.Lib.NumberTheory.EllipticNodalReduction"

/-!
# NOTE-031-002C3: 滑らかに還元しない有限点と中心からの距離

節点の剰余X座標以外には特異点がない。同じX座標の曲線上の点は、Y座標も節点と一致する。
従って有限点が滑らかに還元しないことは、v(x−x₀)<1と同値である。
非整座標の点もHasSmoothReductionに含めたまま、同値を証明する。
この分類は付値環モデルと中心を同じまま扱い、零成分部分加群の加法閉性は主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalReduction
open WeierstrassCurve Affine IsLocalRing
open EllipticCriticalCentre EllipticGoodReductionSeparation

/-- 任意標数の体上で、節点と異なるX座標の曲線上の点は非特異である。
c₄xが全ての特異点で同じ値を取る恒等式を使い、節点量の非零性で約分する。
剰余標数3でも12を約分しない。 -/
theorem nonsingular_of_node_of_x_ne {k : Type*} [Field k] (W : WeierstrassCurve k) (x₀ y₀ : k)
    (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀)
    (hnode : W.b₂ + 12 * x₀ ≠ 0) {x y : k} (h : W.toAffine.Equation x y) (hx : x ≠ x₀) :
    W.toAffine.Nonsingular x y := by
  rw [nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hFX₀, hFY₀⟩ := hs he
  have e₁ : W.toAffine.a₁ = W.a₁ := rfl
  have e₂ : W.toAffine.a₂ = W.a₂ := rfl
  have e₃ : W.toAffine.a₃ = W.a₃ := rfl
  have e₄ : W.toAffine.a₄ = W.a₄ := rfl
  have e₆ : W.toAffine.a₆ = W.a₆ := rfl
  rw [equation_iff, e₁, e₂, e₃, e₄, e₆] at he h
  rw [e₁, e₂, e₄] at hFX₀
  rw [e₁, e₃] at hFY₀
  have hc₄x₀ : W.c₄ * x₀ + (W.b₂ * W.b₄ - 18 * W.b₆) = 0 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x₀) * (W.a₁ * hFY₀ - 2 * hFX₀)
      - 18 * ((2 * y₀ + W.a₁ * x₀ + W.a₃) * hFY₀ - 4 * he)
  have hc₄ : W.c₄ = (W.b₂ + 12 * x₀) ^ 2 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    linear_combination (-24) * (W.a₁ * hFY₀ - 2 * hFX₀)
  rw [nonsingular_iff', equation_iff, e₁, e₂, e₃, e₄, e₆]
  refine ⟨h, ?_⟩
  by_contra hxy
  push Not at hxy
  obtain ⟨hFX, hFY⟩ := hxy
  have hc₄x : W.c₄ * x + (W.b₂ * W.b₄ - 18 * W.b₆) = 0 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * (W.a₁ * hFY - 2 * hFX)
      - 18 * ((2 * y + W.a₁ * x + W.a₃) * hFY - 4 * h)
  have hdiff : (W.b₂ + 12 * x₀) ^ 2 * (x - x₀) = 0 := by
    rw [← hc₄]; linear_combination hc₄x - hc₄x₀
  rcases mul_eq_zero.mp hdiff with h0 | h0
  · exact hnode (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
  · exact hx (sub_eq_zero.mp h0)

/-- 特異点とX座標が同じ曲線上の点は、Y座標も同じである。
Yの二候補は互いの負号だが、特異点では両候補が重なる。 -/
theorem y_eq_of_singular_of_x_eq {k : Type*} [Field k] (W : WeierstrassCurve k)
    {x₀ y₀ x y : k} (he : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (h : W.toAffine.Equation x y) (hx : x = x₀) : y = y₀ := by
  have hneg : y₀ = W.toAffine.negY x₀ y₀ := by
    by_contra hn
    apply hs
    rw [nonsingular_iff]
    exact ⟨he, Or.inr hn⟩
  rcases Y_eq_of_X_eq h he hx with hy | hy
  · exact hy
  · exact hy.trans hneg.symm

private theorem residue_eq_iff_sub_small {L : Type*} [Field L] (A : ValuationSubring L)
    {x z : L} (hx : x ∈ A) (hz : z ∈ A) :
    residue A (⟨x, hx⟩ : A) = residue A (⟨z, hz⟩ : A) ↔ A.valuation (x - z) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff]
  rfl

/-- 同じ整モデルの有限点が滑らかに還元しないことは、中心へのX方向の正の深さと同値である。
左辺が成り立つと非整座標の枝が排除され、右辺からも座標整性を供給する。
剰余方程式・節点量の単元性・同じ中心の剰余特異性を全て実装済みの定理から使う。 -/
theorem not_hasSmoothReduction_some_iff {L : Type*} [Field L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) (C : CriticalCentre A (W.map A.subtype)) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    ¬ HasSmoothReduction W (.some x y h) ↔ A.valuation (x - C.x) < 1 := by
  rw [hasSmoothReduction_some_iff]
  let xr := residue A (⟨C.x, C.x_mem⟩ : A)
  let yr := residue A (⟨C.y, C.y_mem⟩ : A)
  have hC := C.residue_singular W
  have hnode : (W.map (residue A)).b₂ + 12 * xr ≠ 0 := by
    let n : A := W.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)
    have hn : IsUnit n := (A.valuation_eq_one_iff _).mpr C.node_unit
    have hres := (residue_ne_zero_iff_isUnit n).mpr hn
    simpa only [n, map_add, map_mul, map_ofNat, map_b₂] using hres
  constructor
  · intro hnot
    have hx : x ∈ A := by
      by_contra hn
      exact hnot (fun hx' _ => (hn hx').elim)
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hred := equation_residue W (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h.1
    by_contra hv
    have hne : residue A (⟨x, hx⟩ : A) ≠ xr := fun he =>
      hv ((residue_eq_iff_sub_small A hx C.x_mem).mp he)
    have hns := nonsingular_of_node_of_x_ne (W.map (residue A)) xr yr hC.1 hC.2 hnode hred hne
    exact hnot (fun _ _ => hns)
  · intro hv hsm
    have hx : x ∈ A := by
      have hd : x - C.x ∈ A := (A.valuation_le_one_iff _).mp hv.le
      have ha : x - C.x + C.x ∈ A := A.toSubring.add_mem hd C.x_mem
      simpa only [sub_add_cancel] using ha
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hX : residue A (⟨x, hx⟩ : A) = xr := (residue_eq_iff_sub_small A hx C.x_mem).mpr hv
    have hred := equation_residue W (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h.1
    have hY := y_eq_of_singular_of_x_eq (W.map (residue A)) hC.1 hC.2 hred hX
    have hns := hsm hx hy
    rw [hX, hY] at hns
    exact hC.2 hns

/-- 一般ファイバーのモデル一致を明示した、同じ点・中心の深さへの輸送。 -/
theorem not_hasSmoothReduction_some_iff_of_model {L : Type*} [Field L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) (V : WeierstrassCurve L) (hmodel : W.map A.subtype = V)
    (C : CriticalCentre A V) {x y : L} (h : V.toAffine.Nonsingular x y) :
    ¬ HasSmoothReduction W (.some x y h) ↔ A.valuation (x - C.x) < 1 := by
  subst V
  exact not_hasSmoothReduction_some_iff W C h

/-- 滑らかに還元しない有限点では、Y方向も同じ中心へ還元する。
X方向の深さだけでY方向の合同も従い、次の傾きの分母・分子を同じ中心で扱える。 -/
theorem y_small_of_x_small {L : Type*} [Field L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) (C : CriticalCentre A (W.map A.subtype)) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hv : A.valuation (x - C.x) < 1) :
    A.valuation (y - C.y) < 1 := by
  have hx : x ∈ A := by
    have hd := (A.valuation_le_one_iff _).mp hv.le
    have ha : x - C.x + C.x ∈ A := A.toSubring.add_mem hd C.x_mem
    simpa only [sub_add_cancel] using ha
  have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
  have hC := C.residue_singular W
  have hred := equation_residue W (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h.1
  have hX := (residue_eq_iff_sub_small A hx C.x_mem).mpr hv
  exact (residue_eq_iff_sub_small A hy C.y_mem).mp
    (y_eq_of_singular_of_x_eq (W.map (residue A)) hC.1 hC.2 hred hX)

/-- 同じ一般ファイバーのモデル一致を保って、X方向の近さからY方向の近さも輸送する。 -/
theorem y_small_of_x_small_of_model {L : Type*} [Field L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) (V : WeierstrassCurve L) (hmodel : W.map A.subtype = V)
    (C : CriticalCentre A V) {x y : L} (h : V.toAffine.Nonsingular x y)
    (hv : A.valuation (x - C.x) < 1) : A.valuation (y - C.y) < 1 := by
  subst V
  exact y_small_of_x_small W C h hv

end DkMath.Lib.NumberTheory.EllipticNodalReduction
