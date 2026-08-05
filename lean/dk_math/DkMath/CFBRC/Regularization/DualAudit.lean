/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.NegativeInteger
import DkMath.CFBRC.Regularization.AbelLinear

#print "file: DkMath.CFBRC.Regularization.DualAudit"

/-!
# CFBRC regularization dual audit

The finite forward-difference route and the Abel-boundary route are kept
independent until this module.  Their common value is `1/4`.
-/

namespace DkMath.CFBRC.Regularization

open Filter Set Topology

/-- The Abel boundary agrees with the native finite-difference value. -/
theorem alternatingLinearAbelClosed_tendsto_etaNegOneFiniteDifference :
    Tendsto alternatingLinearAbelClosed
      (nhdsWithin 1 (Iio 1))
      (nhds (((etaNegNatFiniteDifference 1 : ℚ) : ℝ))) := by
  simpa using alternatingLinearAbelClosed_tendsto_quarter

/--
Audit 001: two independent regularization routes recover the same finite
eta value, and the native parity normalization is `-1/12`.
-/
theorem cfbrcAnalyticAudit001 :
    Tendsto alternatingLinearAbelClosed
      (nhdsWithin 1 (Iio 1))
      (nhds (((etaNegNatFiniteDifference 1 : ℚ) : ℝ))) ∧
    zetaNegNatFiniteDifference 1 = -1 / 12 := by
  exact ⟨
    alternatingLinearAbelClosed_tendsto_etaNegOneFiniteDifference,
    zetaNegNatFiniteDifference_one⟩

end DkMath.CFBRC.Regularization
