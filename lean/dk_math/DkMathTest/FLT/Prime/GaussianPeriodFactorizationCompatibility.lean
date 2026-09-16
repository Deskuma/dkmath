/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.GaussianPeriodFactorizationProbe
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe

#print "file: DkMathTest.FLT.Prime.GaussianPeriodFactorizationCompatibility"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.TraceOneQuadratic

/-! The new neutral adapter leaves the exact p=11 and p=13 regressions intact. -/

example (z y : ℤ) :
    norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) =
      GTailCyclotomicShell 11 (z - y) y := by
  exact norm11 z y

example (z y : ℤ) :
    norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) =
      GTailCyclotomicShell 13 (z - y) y := by
  exact norm13 z y

#check norm11_direct
#check norm13_direct
#check norm11
#check norm13

end DkMathTest.FLT.Prime
