/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree
import Mathlib.Algebra.Field.ZMod

namespace DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterCharThree

open DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

/-- A translated node: `y² = (x-1)²*(x+1)` over `F₃`, with centre `(1,0)`.
The nonzero centre exercises the division by `b₂` in the explicit formula. -/
def translatedNode : WeierstrassCurve (ZMod 3) := ⟨0, -1, 0, -1, 1⟩

private theorem delta_zero : translatedNode.Δ = 0 := by decide
private theorem c4_ne_zero : translatedNode.c₄ ≠ 0 := by decide

noncomputable def centre : SingularCentre translatedNode :=
  singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero _ delta_zero c4_ne_zero

example : centre.x = 1 := by
  change -translatedNode.b₄ / translatedNode.b₂ = 1
  norm_num [translatedNode, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  exact (div_eq_one_iff_eq (by decide : (-4 : ZMod 3) ≠ 0)).mpr (by decide)

example : centre.y = 0 := by
  change -(translatedNode.a₁ * (-translatedNode.b₄ / translatedNode.b₂) +
    translatedNode.a₃) / 2 = 0
  simp [translatedNode]

example : Nat.card translatedNode.toAffine.Point ≤ 4 := by
  have h := natCard_points_le_card_add_one centre
  simpa only [ZMod.card] using h

#print axioms c4_eq_b2_sq
#print axioms candidate_defect_identity
#print axioms singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero

end DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterCharThree
