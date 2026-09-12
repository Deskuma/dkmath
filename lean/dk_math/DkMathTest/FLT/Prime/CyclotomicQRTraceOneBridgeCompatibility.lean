/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.CyclotomicQRTraceOneBridgeProbe
import DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe

#print "file: DkMathTest.FLT.Prime.CyclotomicQRTraceOneBridgeCompatibility"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

/-! The prior p=3, p=5, and p=7 TraceOne bridge compatibility targets are
replayed by the imported compatibility module; the generic p=3/5/7 endpoint
is independently instantiated by the probe. -/

example : discr (signedPrimeParameter 3) = -3 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 5) = 5 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 7) = -7 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

/-! At p=11 and p=13 the new existential witnesses are kept separate from
the old explicit `A11/B11` and `A13/B13` coordinates.  The old norm targets
remain available through their existing exact theorems. -/

example (z y : ℤ) :
    norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) =
      GTailCyclotomicShell 11 (z - y) y := by
  exact norm11 z y

example (z y : ℤ) :
    norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) =
      GTailCyclotomicShell 13 (z - y) y := by
  exact norm13 z y

end

end DkMathTest.FLT.Prime
