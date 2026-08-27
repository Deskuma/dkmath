/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.DualAudit

#print "file: DkMathTest.CFBRC.Regularization.AbelLinear"

namespace DkMathTest.CFBRC.Regularization

open DkMath.CFBRC.Regularization
open Filter Set Topology

example {r : ℝ} (hr : |r| < 1) :
    HasSum
      (alternatingLinearAbelTerm r)
      (alternatingLinearAbelClosed r) :=
  hasSum_alternatingLinearAbelTerm hr

example :
    Tendsto alternatingLinearAbelClosed
      (nhdsWithin 1 (Iio 1))
      (nhds (1 / 4 : ℝ)) :=
  alternatingLinearAbelClosed_tendsto_quarter

example :
    Tendsto alternatingLinearAbelClosed
      (nhdsWithin 1 (Iio 1))
      (nhds (((etaNegNatFiniteDifference 1 : ℚ) : ℝ))) ∧
    zetaNegNatFiniteDifference 1 = -1 / 12 :=
  cfbrcAnalyticAudit001

#print axioms cfbrcAnalyticAudit001

end DkMathTest.CFBRC.Regularization
