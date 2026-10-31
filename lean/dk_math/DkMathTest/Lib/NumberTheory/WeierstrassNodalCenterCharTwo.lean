/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterCharTwo"

/-!
# 教科書回帰例：標数2の有理節点

`Δ = 0` と `c₄ ≠ 0` から、実際の座標公式で `SingularCentre` を得る。
このテストは、接方向の分離や代数閉包への拡大を仮定していない。
-/

namespace DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterCharTwo

open DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

variable {k : Type*} [Field k] [CharP k 2]

noncomputable example (W : WeierstrassCurve k) (hΔ : W.Δ = 0) (hc4 : W.c₄ ≠ 0) :
    SingularCentre W :=
  singularCentre_of_char_two_of_delta_zero_of_c4_ne_zero W hΔ hc4

#print axioms singularCentre_of_char_two_of_delta_zero_of_c4_ne_zero

end DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterCharTwo
