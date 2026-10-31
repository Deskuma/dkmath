/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.NumberTheory.EllipticNodalSmoothCard"

/-!
# 回帰入口：有理節点からの傾き単射

このテストは分裂接方向を仮定しない。特異中心の方程式と二つの偏微分条件だけから、
滑らかな点群を `Option K` へ単射に送り、有限体では `#K + 1` 以下に抑える。
-/

namespace DkMathTest.Lib.NumberTheory.EllipticNodalSmoothCard

open WeierstrassCurve
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

variable {K : Type*} [Field K] {W : WeierstrassCurve K}

example (C : SingularCentre W) : Function.Injective (SingularCentre.slopeAt C) :=
  SingularCentre.slopeAt_injective C

example [Fintype K] (C : SingularCentre W) :
    Nat.card W.toAffine.Point ≤ Fintype.card K + 1 :=
  natCard_points_le_card_add_one C

example [Finite K] (C : SingularCentre W) : 0 < Nat.card W.toAffine.Point :=
  natCard_points_pos C

#print axioms SingularCentre.translated_equation
#print axioms SingularCentre.slopeAt_injective
#print axioms natCard_points_pos
#print axioms natCard_points_le_card_add_one

end DkMathTest.Lib.NumberTheory.EllipticNodalSmoothCard
