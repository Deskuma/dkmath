/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitPowerSplit

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitHeight"

namespace DkMath.FLT.Seven

noncomputable section

/-! ## Production real-cubic height inequalities

The projective unit classes from the preceding checkpoint are deliberately
not used here.  These inequalities are the analytic algebraic input for the
later embedding bridge.
-/

def H7 (s t : ℝ) : ℝ :=
  s ^ 6 + s ^ 5 * t + s ^ 4 * t ^ 2 + s ^ 3 * t ^ 3 +
    s ^ 2 * t ^ 4 + s * t ^ 5 + t ^ 6

theorem realH7_ge_seven (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    7 * (s * t) ^ 3 ≤ H7 s t := by
  have heq : H7 s t - 7 * (s * t) ^ 3 =
      (s ^ 3 - t ^ 3) ^ 2 +
        s * t * (s ^ 2 - t ^ 2) ^ 2 +
        s ^ 2 * t ^ 2 * (s - t) ^ 2 := by
    unfold H7
    ring
  have hn : 0 ≤ (s ^ 3 - t ^ 3) ^ 2 +
      s * t * (s ^ 2 - t ^ 2) ^ 2 +
      s ^ 2 * t ^ 2 * (s - t) ^ 2 := by
    positivity
  linarith only [heq, hn]

theorem realH7_ge_gap (l r : ℝ) :
    (l - r) ^ 6 ≤ 64 * H7 l r := by
  have heq : 64 * H7 l r - (l - r) ^ 6 =
      7 * (l + r) ^ 6 +
        35 * (l + r) ^ 4 * (l - r) ^ 2 +
        21 * (l + r) ^ 2 * (l - r) ^ 4 := by
    unfold H7
    ring
  have hn : 0 ≤ 7 * (l + r) ^ 6 +
      35 * (l + r) ^ 4 * (l - r) ^ 2 +
      21 * (l + r) ^ 2 * (l - r) ^ 4 := by
    positivity
  linarith only [heq, hn]

/- The current direct packet still needs a production bridge from
   `QuadraticAlgebra.norm cyclotomicRoot.gammaNorm` to all three real
   embeddings of `SevenRealCubic.Field`.  In particular, positivity of its
   rational norm is not used as a substitute for total positivity. -/

end
end DkMath.FLT.Seven
