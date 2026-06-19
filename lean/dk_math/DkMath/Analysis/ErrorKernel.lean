/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.GapGN

#print "file: DkMath.Analysis.ErrorKernel"

/-!
# Exact observation-error correction

The observed value is `base + err`. The full power error is retained by
`gapGN`; no Taylor truncation is used.
-/

namespace DkMath.Analysis

/-- Exact power error between an observed value and its base value. -/
def observedGapError {R : Type*} [CommRing R] (d : ℕ) (base err : R) : R :=
  (base + err) ^ d - base ^ d

/-- The complete observation error factors into `err` times the gap kernel. -/
theorem observedGapError_eq_err_mul_gapGN
    {R : Type*} [CommRing R] (d : ℕ) (base err : R) :
    observedGapError d base err = err * gapGN d base err := by
  exact pow_add_sub_pow_eq_delta_mul_gapGN d base err

/--
Subtracting the exact gap-kernel correction recovers the unobserved base power.
-/
theorem exactCorrection
    {R : Type*} [CommRing R] (d : ℕ) (base err : R) :
    (base + err) ^ d - err * gapGN d base err = base ^ d := by
  rw [pow_add_eq_pow_add_delta_mul_gapGN]
  ring

end DkMath.Analysis
