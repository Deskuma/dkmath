/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

#print "file: DkMath.CFBRC.Regularization.AbelLinear"

/-!
# Abel regularization of the alternating linear moment

Inside the open unit interval, the damped series is an ordinary absolutely
convergent series.  Its boundary value at `r = 1` is then obtained from the
closed rational function; the divergent undamped series is never passed to
`tsum`.
-/

namespace DkMath.CFBRC.Regularization

open Filter Set Topology

/-- The damped alternating linear moment. -/
def alternatingLinearAbelTerm (r : ℝ) (n : ℕ) : ℝ :=
  -(n : ℝ) * (-r) ^ n

/-- Closed form of the damped alternating linear moment. -/
noncomputable def alternatingLinearAbelClosed (r : ℝ) : ℝ :=
  r / (1 + r) ^ 2

/-- Ordinary convergence and closed form throughout the open unit disc. -/
theorem hasSum_alternatingLinearAbelTerm
    {r : ℝ} (hr : |r| < 1) :
    HasSum
      (alternatingLinearAbelTerm r)
      (alternatingLinearAbelClosed r) := by
  have hr' : ‖(-r : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs] using hr
  have hsum :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (r := (-r : ℝ)) hr').neg
  unfold alternatingLinearAbelTerm alternatingLinearAbelClosed
  have hform : -(-r / (1 - -r) ^ 2) = r / (1 + r) ^ 2 := by
    rw [show (1 : ℝ) - -r = 1 + r by ring]
    ring
  rw [hform] at hsum
  simpa [mul_comm] using hsum

/-- The rational closed form is continuous at the Abel boundary. -/
theorem continuousAt_alternatingLinearAbelClosed_one :
    ContinuousAt alternatingLinearAbelClosed 1 := by
  unfold alternatingLinearAbelClosed
  fun_prop (disch := norm_num)

/-- The Abel boundary value of `1 - 2 + 3 - 4 + ⋯` is `1/4`. -/
theorem alternatingLinearAbelClosed_tendsto_quarter :
    Tendsto alternatingLinearAbelClosed
      (nhdsWithin 1 (Iio 1))
      (nhds (1 / 4 : ℝ)) := by
  have h :=
    continuousAt_alternatingLinearAbelClosed_one.continuousWithinAt
      (s := Iio (1 : ℝ))
  have hv : alternatingLinearAbelClosed 1 = (1 / 4 : ℝ) := by
    norm_num [alternatingLinearAbelClosed]
  simpa only [ContinuousWithinAt, hv] using h

end DkMath.CFBRC.Regularization
