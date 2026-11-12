/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean,
blob 38bdee599f8b536cb30402a8d1dbef001a3d89da.
Modified: reuse DkMath coordinate integrality, smooth reduction and actual reduction kernel;
separate valuation-residue arithmetic from coordinate and group constructions.
-/

import DkMath.Lib.NumberTheory.EllipticReductionCoordinates
import DkMath.Lib.NumberTheory.EllipticReductionKernel

#print "file: DkMath.Lib.NumberTheory.EllipticSmoothReduction"

/-!
# NOTE-031-004 第2部: 滑らかな零成分上で還元を加法へ接続する

整点同士では傾きと座標の剰余との可換性を用いる。
極同士は既存の還元核の加法閉性を用いる。整点と極の混合では、
和から整点を引くと極に戻ることから、和の剰余が元の整点の剰余に等しいと示す。
この群論的な逆向きの議論により、形式群の冪級数展開を必要としない。
判別式の単元性、標数零、torsionの位数条件は要求しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticSmoothReduction
open WeierstrassCurve IsLocalRing EllipticReductionSlope
open EllipticGoodReductionSeparation ValuationResidue
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

private lemma some_smoothLocus_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

open Classical in
/-- 整な滑らかな有限点を剰余座標へ写し、それ以外を無限遠点へ写す全域関数。
加法性は後で滑らかな還元を持つ点に限定して証明する。 -/
noncomputable def reducePointSmooth :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      if hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx⟩) then
        .some _ _ hns
      else .zero
    else .zero

/-- 無限遠点の還元は無限遠点である。 -/
@[simp]
theorem reducePointSmooth_zero : reducePointSmooth W 0 = 0 := rfl

/-- 整な滑らかな有限点の還元は実際の剰余座標を持つ有限点である。 -/
theorem reducePointSmooth_some_of_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) :
    reducePointSmooth W (.some x y h) = .some (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) hns := by
  simp only [reducePointSmooth]
  rw [dite_eq_left hx]
  exact dite_eq_left hns

/-- x座標に極を持つ点の還元は無限遠点である。 -/
theorem reducePointSmooth_some_of_notMem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∉ A) :
    reducePointSmooth W (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  exact dite_eq_right hx

/-- 全域関数の特異点分岐。加法性の定理ではこの分岐を除外する。 -/
theorem reducePointSmooth_some_of_singular {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hsing : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
      (residue A ⟨y, hy⟩)) :
    reducePointSmooth W (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  rw [dite_eq_left hx]
  exact dite_eq_right fun hcon => hsing hcon

variable [DecidableEq L]

/-- 還元核の点は滑らかな還元を持ち、剰余で無限遠点へ移る。 -/
theorem kernel_smooth_and_zero {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ EllipticReductionKernel.reductionKernel A W) :
    HasSmoothReduction W P ∧ reducePointSmooth W P = 0 := by
  cases P with
  | zero => exact ⟨hasSmoothReduction_zero W _, rfl⟩
  | some x y h =>
    have hx := (EllipticReductionKernel.some_mem_iff A W h).mp hP
    exact ⟨hasSmoothReduction_of_notMem W h hx, reducePointSmooth_some_of_notMem W h hx⟩

variable [DecidableEq (ResidueField A)]

private lemma addAux_of_mem_of_mem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hP : HasSmoothReduction W (.some x₁ y₁ h₁))
    (hQ : HasSmoothReduction W (.some x₂ y₂ h₂)) :
    HasSmoothReduction W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      reducePointSmooth W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        reducePointSmooth W (.some x₁ y₁ h₁) + reducePointSmooth W (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h₁.1 hx₁
  have hy₂ : y₂ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h₂.1 hx₂
  have hns₁ := (hasSmoothReduction_some_iff W h₁).mp hP hx₁ hy₁
  have hns₂ := (hasSmoothReduction_some_iff W h₂).mp hQ hx₂ hy₂
  by_cases hred : x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits
  · obtain ⟨hredx, hredy⟩ := (residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mpr hred
    by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
    · constructor
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2]
        exact hasSmoothReduction_zero W _
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, reducePointSmooth_zero W,
          reducePointSmooth_some_of_mem W h₁ hx₁ hns₁, reducePointSmooth_some_of_mem W h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
    · have haddX := addX_notMem_of_sub_mem_nonunits_of_smooth W
        ((hasSmoothReduction_some_iff W h₁).mp hP) h₁.1 h₂.1 hx₁ hx₂ hPQ hred.1 hred.2
      constructor
      · rw [Affine.Point.add_some hPQ]
        exact hasSmoothReduction_of_notMem W _ haddX
      · rw [Affine.Point.add_some hPQ, reducePointSmooth_some_of_notMem W _ haddX,
          reducePointSmooth_some_of_mem W h₁ hx₁ hns₁, reducePointSmooth_some_of_mem W h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
  · have hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂) := by
      rintro ⟨hxe, hye⟩
      exact hred ⟨by rw [hxe, sub_self]; exact A.nonunits.zero_mem,
        by rw [hye, sub_self]; exact A.nonunits.zero_mem⟩
    have hredk : ¬(residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) :=
      fun h => hred ((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp h)
    have hXmem : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addX_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hYmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addY_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hXres := residue_addX_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hXmem
    have hYres := residue_addY_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hYmem
    have hns₃ : (W.map (residue A)).toAffine.Nonsingular
        (residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hXmem⟩)
        (residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hYmem⟩) := by
      rw [hXres, hYres]
      exact Affine.nonsingular_add hns₁ hns₂ hredk
    constructor
    · rw [Affine.Point.add_some hPQ, hasSmoothReduction_some_iff W]
      intro hx hy
      exact hns₃
    · rw [Affine.Point.add_some hPQ, reducePointSmooth_some_of_mem W _ hXmem hns₃,
        reducePointSmooth_some_of_mem W h₁ hx₁ hns₁, reducePointSmooth_some_of_mem W h₂ hx₂ hns₂,
        Affine.Point.add_some hredk]
      exact some_smoothLocus_congr hXres hYres _ _

private lemma addAux_of_notMem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    HasSmoothReduction W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      reducePointSmooth W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        reducePointSmooth W (.some x₁ y₁ h₁) + reducePointSmooth W (.some x₂ y₂ h₂) := by
  have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ EllipticReductionKernel.reductionKernel A W :=
    (EllipticReductionKernel.some_mem_iff A W h₁).mpr hx₁
  have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ EllipticReductionKernel.reductionKernel A W :=
    (EllipticReductionKernel.some_mem_iff A W h₂).mpr hx₂
  have hSmem : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈
      EllipticReductionKernel.reductionKernel A W := add_mem hPmem hQmem
  refine ⟨(kernel_smooth_and_zero W hSmem).1, ?_⟩
  rw [(kernel_smooth_and_zero W hSmem).2,
    reducePointSmooth_some_of_notMem W h₁ hx₁, reducePointSmooth_some_of_notMem W h₂ hx₂,
    add_zero]

private lemma addAux_of_mem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (hP : HasSmoothReduction W (.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∉ A) :
    HasSmoothReduction W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      reducePointSmooth W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        reducePointSmooth W (.some x₁ y₁ h₁) + reducePointSmooth W (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h₁.1 hx₁
  have hns₁ := (hasSmoothReduction_some_iff W h₁).mp hP hx₁ hy₁
  have hPn : (W.map A.subtype).toAffine.Nonsingular x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) :=
    (Affine.nonsingular_neg _ _).mpr h₁
  have hPneg : (.some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn :
      (W.map A.subtype).toAffine.Point) = -(.some x₁ y₁ h₁) := (Affine.Point.neg_some h₁).symm
  cases hadd : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) with
  | zero =>
    exfalso
    have hPQ : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) = -(.some x₂ y₂ h₂) :=
      eq_neg_of_add_eq_zero_left hadd
    rw [Affine.Point.neg_some] at hPQ
    simp only [Affine.Point.some.injEq] at hPQ
    exact hx₂ (hPQ.1 ▸ hx₁)
  | some X₃ Y₃ h₃ =>
    by_cases hX₃ : X₃ ∈ A
    · have hY₃ : Y₃ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h₃.1 hX₃
      have hkey : X₃ - x₁ ∈ A.nonunits ∧
          Y₃ - (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) ∈
            A.nonunits := by
        by_contra hcon
        have hSnegP : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
            .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = .some x₂ y₂ h₂ := by
          rw [hPneg, ← hadd]; abel
        have hSP : ¬(X₃ = x₁ ∧
            Y₃ = (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁)) := by
          rintro ⟨hX, hY⟩
          have h0 : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
              .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = 0 :=
            Affine.Point.add_of_Y_eq hX hY
          rw [hSnegP] at h0
          exact Affine.Point.some_ne_zero h₂ h0
        have haddX : (W.map A.subtype).toAffine.addX X₃ x₁
            ((W.map A.subtype).toAffine.slope X₃ x₁ Y₃
              ((W.map A.subtype).toAffine.negY x₁ y₁)) ∈ A :=
          addX_mem_of_not_inverse h₃.1 hPn.1 hX₃ hx₁ hcon
        rw [Affine.Point.add_some hSP] at hSnegP
        simp only [Affine.Point.some.injEq] at hSnegP
        exact hx₂ (hSnegP.1 ▸ haddX)
      rw [Affine.negY_negY] at hkey
      have hXres : residue A ⟨X₃, hX₃⟩ = residue A ⟨x₁, hx₁⟩ :=
        (residue_eq_residue_iff_sub_mem_nonunits A hX₃ hx₁).mpr hkey.1
      have hYres : residue A ⟨Y₃, hY₃⟩ = residue A ⟨y₁, hy₁⟩ :=
        (residue_eq_residue_iff_sub_mem_nonunits A hY₃ hy₁).mpr hkey.2
      have hnsS : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨X₃, hX₃⟩)
          (residue A ⟨Y₃, hY₃⟩) := by
        rw [hXres, hYres]
        exact hns₁
      constructor
      · rw [hasSmoothReduction_some_iff W]
        intro hx hy
        exact hnsS
      · rw [reducePointSmooth_some_of_mem W h₃ hX₃ hnsS,
          reducePointSmooth_some_of_notMem W h₂ hx₂,
          reducePointSmooth_some_of_mem W h₁ hx₁ hns₁, add_zero]
        exact some_smoothLocus_congr hXres hYres _ _
    · exfalso
      have hS : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) ∈ EllipticReductionKernel.reductionKernel A W :=
        (EllipticReductionKernel.some_mem_iff A W h₃).mpr hX₃
      have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ EllipticReductionKernel.reductionKernel A W :=
        (EllipticReductionKernel.some_mem_iff A W h₂).mpr hx₂
      have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ EllipticReductionKernel.reductionKernel A W := by
        have hPeq : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) =
            .some X₃ Y₃ h₃ - .some x₂ y₂ h₂ := by
          rw [← hadd]; abel
        rw [hPeq]
        exact sub_mem hS hQmem
      exact ((EllipticReductionKernel.some_mem_iff A W h₁).mp hPmem) hx₁

/-- 滑らかな還元を持つ点の和も滑らかであり、実際の還元は加法と可換となる。
整点同士・極同士・整点と極の三場合を既存の還元核で接続する。 -/
theorem smooth_add_and_reduce {P Q : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) (hQ : HasSmoothReduction W Q) :
    HasSmoothReduction W (P + Q) ∧
      reducePointSmooth W (P + Q) = reducePointSmooth W P + reducePointSmooth W Q := by
  cases P with
  | zero => simpa only [← Affine.Point.zero_def, zero_add, reducePointSmooth_zero] using
      And.intro hQ (Eq.refl (reducePointSmooth W Q))
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simpa only [← Affine.Point.zero_def, add_zero, reducePointSmooth_zero] using
        And.intro hP (Eq.refl (reducePointSmooth W (.some x₁ y₁ h₁)))
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact addAux_of_mem_of_mem W h₁ h₂ hx₁ hx₂ hP hQ
      · exact addAux_of_mem_of_notMem W h₁ h₂ hP hx₁ hx₂
      · rw [add_comm (Affine.Point.some x₁ y₁ h₁) (Affine.Point.some x₂ y₂ h₂)]
        obtain ⟨hs, hr⟩ := addAux_of_mem_of_notMem W h₂ h₁ hQ hx₂ hx₁
        exact ⟨hs, hr.trans (add_comm _ _)⟩
      · exact addAux_of_notMem_of_notMem W h₁ h₂ hx₁ hx₂

omit [DecidableEq L] [DecidableEq (ResidueField A)] in
/-- 反転は滑らかな還元を保つ。有限座標の反転と剰余の可換性から従う。 -/
theorem smooth_neg {P : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) : HasSmoothReduction W (-P) := by
  classical
  cases P with
  | zero => simpa only [← Affine.Point.zero_def, neg_zero] using hP
  | some x y h =>
    rw [Affine.Point.neg_some, hasSmoothReduction_some_iff]
    intro hx hy'
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hns := (hasSmoothReduction_some_iff W h).mp hP hx hy
    have hkey : residue A (⟨(W.map A.subtype).toAffine.negY x y, hy'⟩ : A) =
        (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
      rw [residue_eq_of_coe_eq A hy' (v := W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩)
        (coe_negY hx hy).symm]
      exact residue_negY hx hy
    rw [hkey]
    exact (Affine.nonsingular_neg ..).mpr hns

/-- 一般ファイバーの点のうち滑らかな還元を持つ点がなす、実際の加法部分群。 -/
def zeroComponentSubgroup : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | HasSmoothReduction W P}
  zero_mem' := hasSmoothReduction_zero W _
  add_mem' := fun hP hQ => (smooth_add_and_reduce W hP hQ).1
  neg_mem' := fun hP => smooth_neg W hP

/-- 零成分部分群の条件は、既存の座標的な滑らかさの条件そのものである。 -/
theorem mem_zeroComponentSubgroup_iff {P : (W.map A.subtype).toAffine.Point} :
    P ∈ zeroComponentSubgroup W ↔ HasSmoothReduction W P := Iff.rfl

/-- 零成分上の還元は剰余曲線の滑らかな点群への加法準同型である。
ここから自然数倍との可換性を一般の群準同型の定理として利用できる。 -/
noncomputable def zeroComponentReduction :
    zeroComponentSubgroup W →+ (W.map (residue A)).toAffine.Point where
  toFun P := reducePointSmooth W P.1
  map_zero' := reducePointSmooth_zero W
  map_add' P Q := (smooth_add_and_reduce W P.2 Q.2).2

/-- 滑らかな還元を持つp-torsionを実際に還元すると、剰余上でもp-torsionとなる。
標数零の除法多項式を剰余標数へ流用せず、加法準同型によって倍算を運ぶ。 -/
theorem nsmul_reduce_eq_zero {P : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) (n : ℕ) (hn : n • P = 0) :
    n • reducePointSmooth W P = 0 := by
  let Q : zeroComponentSubgroup W := ⟨P, hP⟩
  have hQ : n • Q = 0 := Subtype.ext hn
  have he := congrArg (zeroComponentReduction W) hQ
  change n • (zeroComponentReduction W) Q = 0
  simpa only [map_nsmul, map_zero] using he

end DkMath.Lib.NumberTheory.EllipticSmoothReduction
