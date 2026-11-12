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

import DkMath.Lib.NumberTheory.EllipticReductionSlope

#print "file: DkMath.Lib.NumberTheory.EllipticReductionCoordinates"

/-!
# NOTE-031-004 第2部: 和の二座標と剰余の可換性

前章の整な傾きを付値環内の加法公式へ代入し、和の二座標の整性を得る。
同じ公式へ剰余写像を適用すると、剰余点の和の二座標と一致する。
逆の剰余点の場合は本章から除き、差に極が生じる既存の補題で扱う。
-/
namespace DkMath.Lib.NumberTheory.EllipticReductionSlope
open WeierstrassCurve IsLocalRing ValuationResidue
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
  [DecidableEq L] [DecidableEq (ResidueField A)]

omit [DecidableEq (ResidueField A)] in
/-- 逆の剰余点でない整点の和のx座標は整である。 -/
theorem addX_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  classical
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hX_coe]
  exact SetLike.coe_mem _

omit [DecidableEq (ResidueField A)] in
/-- 逆の剰余点でない整点の和のy座標も整である。 -/
theorem addY_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  classical
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hy₁ : y₁ ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h₁ hx₁
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hY_coe]
  exact SetLike.coe_mem _


/-- 整な和のx座標の剰余は、剰余曲線の加法公式のx座標に等しい。 -/
theorem residue_addX_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        residue_eq_of_coe_eq A hmem hX_coe
    _ = (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addX (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']


/-- 整な和のy座標の剰余は、同じ剰余曲線の加法公式のy座標に等しい。 -/
theorem residue_addY_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        residue_eq_of_coe_eq A hmem hY_coe
    _ = (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addY (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A)
          (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']

end DkMath.Lib.NumberTheory.EllipticReductionSlope
