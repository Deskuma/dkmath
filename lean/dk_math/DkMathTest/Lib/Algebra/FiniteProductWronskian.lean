/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.Algebra.FiniteProductWronskian

#print "file: DkMathTest.Lib.Algebra.FiniteProductWronskian"

/-!
# 有限積 Wronskian 恒等式の回帰入口

半核や楕円曲線を固定せず、一般の可換環上の多項式分子・分母に対して
共通分母恒等式を呼び出せることを確認する。曲線固有の `xCorrection` は
この一般代数層の上に別途特殊化される。
-/
namespace DkMathTest.FiniteProductWronskian

open Polynomial
open scoped BigOperators
open DkMath.Lib.Algebra.FiniteProductWronskian

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

example (s : Finset ι) (N D : ι → R[X]) :
    (commonNumerator s N D).derivative * commonDenominator s D -
        commonNumerator s N D * (commonDenominator s D).derivative =
      (commonDenominator s D) ^ 2 +
        ∑ i ∈ s, (erasedProduct s D i) ^ 2 *
          ((N i).derivative * D i - N i * (D i).derivative) :=
  commonNumerator_wronskian_eq s N D

end DkMathTest.FiniteProductWronskian
