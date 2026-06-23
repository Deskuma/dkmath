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
-/

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/-- The exact boundary-depth factor observed at a dyadic phase node. -/
def dyadicPhaseDepth (n k : ℕ) : ℝ :=
  phaseDepth (dyadicPhaseNode n k)

/-- The boundary-restoring normalization observed at a dyadic phase node. -/
def dyadicPhaseNormalization (n k : ℕ) : ℝ :=
  phaseNormalization (dyadicPhaseNode n k)

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
        1 / (2 * (dyadicPhaseDenom n : ℝ) ^ 2) := by
  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
  simp [dyadicPhaseDepth, dyadicPhaseNode, dyadicPhaseDenom, phaseDepth,
    pow_succ]
  field_simp
  ring

end

end DkMath.Analysis.DkNNRealQ
