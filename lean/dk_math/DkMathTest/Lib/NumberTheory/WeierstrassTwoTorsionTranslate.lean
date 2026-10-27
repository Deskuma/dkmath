/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassTwoTorsionTranslate"

/-! 有理点 `(2,4)` を持つ曲線で、2捩れ根による平行移動公式を検査する。 -/
namespace WeierstrassTwoTorsionTranslateTest
open WeierstrassCurve
open DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate

def curve : WeierstrassCurve ℚ := ⟨0, 5, 0, -6, 0⟩

private theorem curve_point : curve.toAffine.Equation 2 4 := by
  norm_num [curve, WeierstrassCurve.Affine.equation_iff]

private theorem curve_a₁ : curve.a₁ = 0 := rfl
private theorem curve_a₃ : curve.a₃ = 0 := rfl
private theorem curve_σ₁ : (0 : ℚ) + 1 + (-6) = -curve.a₂ := by norm_num [curve]
private theorem curve_σ₂ : (0 : ℚ) * 1 + 0 * (-6) + 1 * (-6) = curve.a₄ := by norm_num [curve]
private theorem curve_σ₃ : (0 : ℚ) * 1 * (-6) = -curve.a₆ := by norm_num [curve]

example : curve.toAffine.addX 0 2 (curve.toAffine.slope 0 2 0 4) = -3 := by
  have h := addX_two_torsion_sub_root curve curve_a₁ curve_a₃ curve_σ₁ curve_σ₂ curve_σ₃
    curve_point (by norm_num)
  have h' : curve.toAffine.addX 0 2 (curve.toAffine.slope 0 2 0 4) - 1 = -4 := by
    norm_num [curve] at h ⊢
  linarith

example : (1 - curve.toAffine.addX 0 2 (curve.toAffine.slope 0 2 0 4)) * (2 - 0) =
    -((0 - 1) * (2 - (-6))) := by
  exact translated_root_difference curve curve_a₁ curve_a₃ curve_σ₁ curve_σ₂ curve_σ₃
    curve_point (by norm_num)

example : curve.toAffine.addX 0 2 (curve.toAffine.slope 0 2 0 4) - 0 =
    ((0 : ℚ) - 1) * (0 - (-6)) / (2 - 0) := by
  exact addX_two_torsion_sub_self curve curve_a₁ curve_a₃ curve_σ₁ curve_σ₂ curve_σ₃
    curve_point (by norm_num)

#print axioms DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate.addX_two_torsion_sub_root
#print axioms DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate.translated_root_difference
end WeierstrassTwoTorsionTranslateTest
