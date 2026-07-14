/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DDyadic
import DkMath.Analysis.DkReal.SemanticCF2DNormalize

#print "file: DkMath.Analysis.DkReal.SemanticCF2DRefinement"

/-!
# Finite observations under dyadic phase refinement

This module evaluates the exact phase-depth and boundary-normalization
profiles on the finite dyadic mesh. It records the laws forced by the mesh
before choosing any aggregate correction.

The key new identity concerns an odd child. Since `phaseDepth` is quadratic,
its value at the midpoint of adjacent parent nodes is their average depth
minus an explicit positive mesh correction. This is a finite algebraic
refinement law, not an asymptotic or Gaussian statement.

These observations inherit noncomputability from the real-valued dyadic node
and, for normalization, from real square root. Their formulas remain exact;
computability requires a separate rational observation layer.
-/

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/-- The exact boundary-depth factor observed at a dyadic phase node. -/
def dyadicPhaseDepth (n k : ℕ) : ℝ :=
  phaseDepth (dyadicPhaseNode n k)

/-- The boundary-restoring normalization observed at a dyadic phase node. -/
def dyadicPhaseNormalization (n k : ℕ) : ℝ :=
  phaseNormalization (dyadicPhaseNode n k)

/--
The local quadratic defect introduced at every odd child of refinement level
`n + 1`.
-/
def dyadicPhaseDepthDefect (n : ℕ) : ℝ :=
  1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2)

/-- The local dyadic depth defect is strictly positive. -/
theorem dyadicPhaseDepthDefect_pos (n : ℕ) :
    0 < dyadicPhaseDepthDefect n := by
  have hdenom : (0 : ℝ) < dyadicPhaseDenom n := by
    exact_mod_cast dyadicPhaseDenom_pos n
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (sq_pos_of_pos hdenom)

/-- Complementary dyadic nodes have equal boundary depth. -/
theorem dyadicPhaseDepth_reflect
    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
    dyadicPhaseDepth n (dyadicPhaseDenom n - k) =
      dyadicPhaseDepth n k := by
  exact phaseDepth_dyadic_reflect hk

/-- An even child retains the exact depth of its parent. -/
@[simp]
theorem dyadicPhaseDepth_child_even (n k : ℕ) :
    dyadicPhaseDepth (n + 1) (2 * k) = dyadicPhaseDepth n k := by
  simp [dyadicPhaseDepth]

/-- Complementary dyadic nodes require the same boundary normalization. -/
theorem dyadicPhaseNormalization_reflect
    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
    dyadicPhaseNormalization n (dyadicPhaseDenom n - k) =
      dyadicPhaseNormalization n k := by
  rw [dyadicPhaseNormalization, dyadicPhaseNormalization,
    dyadicPhaseNode_reflect hk, phaseNormalization_one_sub]

/-- An even child retains the exact normalization of its parent. -/
@[simp]
theorem dyadicPhaseNormalization_child_even (n k : ℕ) :
    dyadicPhaseNormalization (n + 1) (2 * k) =
      dyadicPhaseNormalization n k := by
  simp [dyadicPhaseNormalization]

/--
The odd-child depth is the average of adjacent parent depths minus the exact
quadratic mesh correction `1 / (2 * (2^n)^2)`.
-/
theorem dyadicPhaseDepth_child_odd
    (n k : ℕ) :
    dyadicPhaseDepth (n + 1) (2 * k + 1) =
      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
        dyadicPhaseDepthDefect n := by
  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
  simp [dyadicPhaseDepth, dyadicPhaseDepthDefect, dyadicPhaseNode,
    dyadicPhaseDenom, phaseDepth, pow_succ]
  field_simp
  ring

/--
The odd-child law restricted to an actual parent interval of the dyadic mesh.
-/
theorem dyadicPhaseDepth_child_odd_of_lt
    {n k : ℕ} (_hk : k < dyadicPhaseDenom n) :
    dyadicPhaseDepth (n + 1) (2 * k + 1) =
      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 -
        dyadicPhaseDepthDefect n :=
  dyadicPhaseDepth_child_odd n k

/-- Every genuine odd child lies strictly below its adjacent-parent average. -/
theorem dyadicPhaseDepth_child_odd_lt_average
    {n k : ℕ} (_hk : k < dyadicPhaseDenom n) :
    dyadicPhaseDepth (n + 1) (2 * k + 1) <
      (dyadicPhaseDepth n k + dyadicPhaseDepth n (k + 1)) / 2 := by
  rw [dyadicPhaseDepth_child_odd n k]
  exact sub_lt_self _ (dyadicPhaseDepthDefect_pos n)

/--
The total defect over all odd children introduced at level `n + 1` is
`1 / (2 * 2^n)`.

There are `2^n` parent intervals, each carrying the same inverse-square local
defect. This is a finite identity and makes no convergence claim.
-/
theorem sum_dyadicPhaseDepthDefect (n : ℕ) :
    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
      1 / (2 * (dyadicPhaseDenom n : ℝ)) := by
  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
  simp [dyadicPhaseDepthDefect]
  field_simp

/-- The total odd-child depth defect introduced at refinement level `n + 1`. -/
def totalDyadicPhaseDepthDefect (n : ℕ) : ℝ :=
  1 / (2 * (dyadicPhaseDenom n : ℝ))

/-- The finite odd-child sum is the named total level defect. -/
theorem sum_dyadicPhaseDepthDefect_eq_total (n : ℕ) :
    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
      totalDyadicPhaseDepthDefect n :=
  sum_dyadicPhaseDepthDefect n

/-- Closed geometric form of the total defect introduced at one level. -/
theorem totalDyadicPhaseDepthDefect_eq_pow (n : ℕ) :
    totalDyadicPhaseDepthDefect n = (1 / 2 : ℝ) ^ (n + 1) := by
  simp [totalDyadicPhaseDepthDefect, dyadicPhaseDenom, pow_succ]

/-- Every per-level total depth defect is strictly positive. -/
theorem totalDyadicPhaseDepthDefect_pos (n : ℕ) :
    0 < totalDyadicPhaseDepthDefect n := by
  rw [totalDyadicPhaseDepthDefect_eq_pow]
  positivity

/--
The cumulative depth defect through the first `m` refinement levels.

The range convention includes levels `0, ..., m - 1`.
-/
def cumulativeDyadicPhaseDepthDefect (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, totalDyadicPhaseDepthDefect n

/-- Exact finite geometric formula for the cumulative depth defect. -/
theorem cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
    cumulativeDyadicPhaseDepthDefect m = 1 - (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero =>
      simp [cumulativeDyadicPhaseDepthDefect]
  | succ m ih =>
      rw [cumulativeDyadicPhaseDepthDefect, Finset.sum_range_succ]
      rw [show (∑ n ∈ Finset.range m, totalDyadicPhaseDepthDefect n) =
          cumulativeDyadicPhaseDepthDefect m by
        rfl, ih, totalDyadicPhaseDepthDefect_eq_pow]
      ring

/-- The unrecovered depth after `m` levels is exactly the dyadic tail. -/
theorem one_sub_cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
    1 - cumulativeDyadicPhaseDepthDefect m = (1 / 2 : ℝ) ^ m := by
  rw [cumulativeDyadicPhaseDepthDefect_eq]
  ring

/-- Every finite cumulative depth defect is nonnegative. -/
theorem cumulativeDyadicPhaseDepthDefect_nonneg (m : ℕ) :
    0 ≤ cumulativeDyadicPhaseDepthDefect m := by
  rw [cumulativeDyadicPhaseDepthDefect_eq]
  have hpow : (1 / 2 : ℝ) ^ m ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- Every finite cumulative depth defect remains strictly below its limit one. -/
theorem cumulativeDyadicPhaseDepthDefect_lt_one (m : ℕ) :
    cumulativeDyadicPhaseDepthDefect m < 1 := by
  rw [cumulativeDyadicPhaseDepthDefect_eq]
  exact sub_lt_self _ (by positivity)

end

end DkMath.Analysis.DkNNRealQ
