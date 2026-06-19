/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.ErrorKernel
import DkMath.Analysis.GapFill

#print "file: DkMath.Analysis.RealBridge"

/-!
# Bridge to Mathlib real analysis

The definitions in `DkMath.Analysis` are algebraic and remain meaningful over
general rings. This file records their standard real interpretation and begins
the bridge to Mathlib's topological and analytic API.
-/

namespace DkMath.Analysis

/-- The exact `gapGN` power decomposition specialized to real numbers. -/
theorem real_pow_add_eq_pow_add_delta_mul_gapGN
    (d : ℕ) (base delta : ℝ) :
    (base + delta) ^ d = base ^ d + delta * gapGN d base delta :=
  pow_add_eq_pow_add_delta_mul_gapGN d base delta

/-- The exact observation correction specialized to real numbers. -/
theorem real_exactCorrection (d : ℕ) (base err : ℝ) :
    (base + err) ^ d - err * gapGN d base err = base ^ d :=
  exactCorrection d base err

/-- The affine gap scan is continuous in its scan parameter. -/
theorem continuous_gapLine (u₁ u₂ : ℝ) :
    Continuous (fun t : ℝ => gapLine u₁ u₂ t) := by
  unfold gapLine
  fun_prop

/-- The powered gap fill is continuous in its scan parameter. -/
theorem continuous_gapFill (d : ℕ) (u₁ u₂ : ℝ) :
    Continuous (fun t : ℝ => gapFill d u₁ u₂ t) := by
  unfold gapFill gapLine
  fun_prop

/--
The real gap fill maps the unit scan interval into the powered endpoint
interval when the endpoints are nonnegative and ordered.
-/
theorem mapsTo_gapFill_Icc_of_nonneg
    {d : ℕ} {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
    Set.MapsTo (fun t : ℝ => gapFill d u₁ u₂ t)
      (Set.Icc 0 1) (Set.Icc (u₁ ^ d) (u₂ ^ d)) := by
  intro t ht
  exact gapFill_mem_Icc_of_nonneg ht hu₁ hle

end DkMath.Analysis
