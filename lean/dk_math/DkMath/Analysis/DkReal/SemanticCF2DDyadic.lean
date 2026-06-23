/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DPhase

#print "file: DkMath.Analysis.DkReal.SemanticCF2DDyadic"

/-!
# Finite dyadic refinement of one semantic phase

This module introduces only the finite combinatorics required before any
refinement limit is considered. At level `n`, the phase interval is sampled
at

`dyadicPhaseNode n k = k / 2^n`.

The endpoint, reflection, and parent-child laws are exact algebraic
identities. No infinite product, logarithmic correction, Gaussian weight, or
identification with `pi` is assumed here.
-/

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/-- The number of equal subintervals in the `n`th dyadic phase partition. -/
def dyadicPhaseDenom (n : ℕ) : ℕ :=
  2 ^ n

/-- The `k`th real node of the `n`th dyadic phase partition. -/
def dyadicPhaseNode (n k : ℕ) : ℝ :=
  (k : ℝ) / (dyadicPhaseDenom n : ℝ)

/-- Every dyadic phase denominator is strictly positive. -/
theorem dyadicPhaseDenom_pos (n : ℕ) :
    0 < dyadicPhaseDenom n := by
  simp [dyadicPhaseDenom]

/-- The first node of every dyadic partition is the phase origin. -/
@[simp]
theorem dyadicPhaseNode_zero (n : ℕ) :
    dyadicPhaseNode n 0 = 0 := by
  simp [dyadicPhaseNode]

/-- The last node of every dyadic partition is the phase endpoint. -/
@[simp]
theorem dyadicPhaseNode_last (n : ℕ) :
    dyadicPhaseNode n (dyadicPhaseDenom n) = 1 := by
  simp [dyadicPhaseNode, dyadicPhaseDenom]

/-- Every indexed partition node lies in the closed phase interval. -/
theorem dyadicPhaseNode_mem_unitInterval
    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
    dyadicPhaseNode n k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by exact_mod_cast dyadicPhaseDenom_pos n)).2
    exact_mod_cast hk

/--
Complementary node indices are reflected about the phase midpoint.

The bound ensures that natural subtraction represents the intended
complement rather than truncated subtraction.
-/
theorem dyadicPhaseNode_reflect
    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
    dyadicPhaseNode n (dyadicPhaseDenom n - k) =
      1 - dyadicPhaseNode n k := by
  rw [dyadicPhaseNode, dyadicPhaseNode, Nat.cast_sub hk]
  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
  field_simp

/-- Every even child node is exactly its parent node. -/
@[simp]
theorem dyadicPhaseNode_child_even (n k : ℕ) :
    dyadicPhaseNode (n + 1) (2 * k) = dyadicPhaseNode n k := by
  simp [dyadicPhaseNode, dyadicPhaseDenom, pow_succ]
  ring

/-- Every odd child node is the midpoint of two adjacent parent nodes. -/
theorem dyadicPhaseNode_child_odd_mid (n k : ℕ) :
    dyadicPhaseNode (n + 1) (2 * k + 1) =
      (dyadicPhaseNode n k + dyadicPhaseNode n (k + 1)) / 2 := by
  simp [dyadicPhaseNode, dyadicPhaseDenom, pow_succ]
  ring

/-- The exact phase-depth observation agrees at complementary dyadic nodes. -/
theorem phaseDepth_dyadic_reflect
    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
    phaseDepth (dyadicPhaseNode n (dyadicPhaseDenom n - k)) =
      phaseDepth (dyadicPhaseNode n k) := by
  rw [dyadicPhaseNode_reflect hk, phaseDepth_one_sub]

end

end DkMath.Analysis.DkNNRealQ
