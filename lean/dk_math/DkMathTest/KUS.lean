/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS

#print "file: DkMathTest.KUS"

namespace DkMathTest.KUS

open DkMath.KUS

abbrev support := DkMath.KUS.Examples.toySupport
abbrev a : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  ofNat support 3
abbrev b : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  ofNat support 4

example : toNat DkMath.KUS.Examples.toyX = 5 := by
  exact DkMath.KUS.Examples.toyX_toNat

example : toNat DkMath.KUS.Examples.toyMul = 10 := by
  exact DkMath.KUS.Examples.toyMul_toNat

example : extract DkMath.KUS.Examples.toyMul = support := by
  exact DkMath.KUS.Examples.toyMul_extract

example :
    toNat (kusAdd a b (by simp [SameSupport])) = 7 := by
  simp [kusAdd]

example :
    extract (kusAdd a b (by simp [SameSupport])) = support := by
  simp [kusAdd]

example :
    toNat (kusMul a b (by simp [SameSupport])) = 12 := by
  simp [kusMul]

example :
    extract (kusMul a b (by simp [SameSupport])) = support := by
  simp [kusMul]

example :
    kusMul DkMath.KUS.Examples.toyX (oneState support)
      (by simp [SameSupport, oneState, DkMath.KUS.Examples.toyX])
      = DkMath.KUS.Examples.toyX := by
  simpa [DkMath.KUS.Examples.toyX] using (kusMul.mul_one (x := DkMath.KUS.Examples.toyX))

example :
    extract (kusMul DkMath.KUS.Examples.toyX (zeroState support)
      (by simp [SameSupport, DkMath.KUS.Examples.toyX])) = support := by
  simp [kusMul, DkMath.KUS.Examples.toyX]

end DkMathTest.KUS
