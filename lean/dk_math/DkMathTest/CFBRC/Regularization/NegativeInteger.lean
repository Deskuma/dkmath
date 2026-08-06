/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.NegativeInteger

#print "file: DkMathTest.CFBRC.Regularization.NegativeInteger"

namespace DkMathTest.CFBRC.Regularization

open DkMath.CFBRC.Regularization

example : etaNegNatFiniteDifference 0 = 1 / 2 := by simp
example : etaNegNatFiniteDifference 1 = 1 / 4 := by simp
example : etaNegNatFiniteDifference 2 = 0 := by simp
example : etaNegNatFiniteDifference 3 = -1 / 8 := by simp

example : zetaNegNatFiniteDifference 0 = -1 / 2 := by simp
example : zetaNegNatFiniteDifference 1 = -1 / 12 := by simp
example : zetaNegNatFiniteDifference 2 = 0 := by simp
example : zetaNegNatFiniteDifference 3 = 1 / 120 := by simp

#print axioms cfbrcNative_zeta_neg_one_eq_neg_one_div_twelve

end DkMathTest.CFBRC.Regularization
