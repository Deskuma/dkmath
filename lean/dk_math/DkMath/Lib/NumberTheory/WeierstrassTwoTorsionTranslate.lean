/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
The affine translation argument is adapted from
S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean,
blob 0c42a9282f1033d6d64cc213bb1f7c7c52b17d1e.
-/

import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots

#print "file: DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate"

/-!
# 2捩れ根での平行移動 x 座標

[DkMath.Lib] 2捩れ点 `(e,0)` と一般点 `(x,y)` の和の x 座標を、
二つの他の2捩れ根で表す。これは商写像の判別式積公式で現れる
`(e_k - ξ) (x-e_j)` 型の関係を、実際の affine 加法から供給する補題である。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate
open WeierstrassCurve WeierstrassCurve.Affine

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k)
/-- [DkMath.Lib] 2捩れ根 `e₁` と任意の点の和の x 座標の閉形式。
分母 `x-e₁` の非零性だけを仮定し、三根の対称式を使って分母を払う。 -/
theorem addX_two_torsion_sub_root
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {e₁ e₂ e₃ x y : k}
    (hσ₁ : e₁ + e₂ + e₃ = -W.a₂)
    (hσ₂ : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = W.a₄)
    (hσ₃ : e₁ * e₂ * e₃ = -W.a₆)
    (he : W.toAffine.Equation x y) (hxe : x ≠ e₁) :
    W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y) - e₂ =
      (e₁ - e₂) * (x - e₃) / (x - e₁) := by
  classical
  have heq : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    rw [Affine.equation_iff, ha₁, ha₃] at he
    linear_combination he
  have hd : x - e₁ ≠ 0 := sub_ne_zero.mpr hxe
  rw [Affine.slope_of_X_ne (fun h => hxe h.symm)]
  simp only [Affine.addX, WeierstrassCurve.toAffine, ha₁]
  field_simp
  linear_combination (norm := ring_nf) (x - e₁) * heq
    + (2 * e₁ * x ^ 2 - 3 * e₁ ^ 2 * x + e₁ ^ 3) * hσ₁
    + (e₁ * x - x ^ 2) * hσ₂ + (x - e₁) * hσ₃

/-- [DkMath.Lib] 根差関係を平行移動の x 座標へ書き換える。
`ξ = x((e₁,0)+(x,y))` と置けば、判別式消去に必要な一因子が得られる。 -/
theorem translated_root_difference
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {e₁ e₂ e₃ x y : k}
    (hσ₁ : e₁ + e₂ + e₃ = -W.a₂)
    (hσ₂ : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = W.a₄)
    (hσ₃ : e₁ * e₂ * e₃ = -W.a₆)
    (he : W.toAffine.Equation x y) (hxe : x ≠ e₁) :
    (e₂ - W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y)) * (x - e₁) =
      -((e₁ - e₂) * (x - e₃)) := by
  have h := addX_two_torsion_sub_root W ha₁ ha₃ hσ₁ hσ₂ hσ₃ he hxe
  have hd : x - e₁ ≠ 0 := sub_ne_zero.mpr hxe
  rw [← sub_eq_zero] at h ⊢
  field_simp [hd] at h ⊢
  linear_combination -h

/-- [DkMath.Lib] 自分自身を引いた版は、半核の各点について使う標準形である。 -/
theorem addX_two_torsion_sub_self
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {e₁ e₂ e₃ x y : k}
    (hσ₁ : e₁ + e₂ + e₃ = -W.a₂)
    (hσ₂ : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = W.a₄)
    (hσ₃ : e₁ * e₂ * e₃ = -W.a₆)
    (he : W.toAffine.Equation x y) (hxe : x ≠ e₁) :
    W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y) - e₁ =
      (e₁ - e₂) * (e₁ - e₃) / (x - e₁) := by
  have h := addX_two_torsion_sub_root W ha₁ ha₃ hσ₁ hσ₂ hσ₃ he hxe
  have hd : x - e₁ ≠ 0 := sub_ne_zero.mpr hxe
  have h' : (W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y) - e₁) * (x - e₁) =
      (e₁ - e₂) * (e₁ - e₃) := by
    calc
      (W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y) - e₁) * (x - e₁) =
          (W.toAffine.addX e₁ x (W.toAffine.slope e₁ x 0 y) - e₂) * (x - e₁) +
            (e₂ - e₁) * (x - e₁) := by ring
      _ = (e₁ - e₂) * (x - e₃) + (e₂ - e₁) * (x - e₁) := by
        rw [h]
        field_simp [hd]
      _ = (e₁ - e₂) * (e₁ - e₃) := by ring
  field_simp [hd]
  exact h'

end DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate
