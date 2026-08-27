/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.RiemannZetaOracleAudit

#print "file: DkMathTest.CFBRC.Regularization.RiemannZetaOracleAudit"

namespace DkMathTest.CFBRC.Regularization

open DkMath.CFBRC.Regularization

example :
    ((zetaNegNatFiniteDifference 1 : ℚ) : ℂ) =
      riemannZeta (-(1 : ℂ)) :=
  cfbrcNative_zetaNegOne_eq_riemannZeta

#print axioms cfbrcNative_zetaNegOne_eq_riemannZeta

end DkMathTest.CFBRC.Regularization
