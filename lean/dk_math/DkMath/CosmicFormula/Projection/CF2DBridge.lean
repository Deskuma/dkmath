/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.CosmicFormula.Projection.Basic
import DkMath.CosmicFormula.Rotation.CF2D.CycleDivision

#print "file: DkMath.CosmicFormula.Projection.CF2DBridge"

/-!
# Cosmic Projection / CF2D bridge

At the finite positive `k`-division, the projection coordinate at `P = k - 1`
has the same scalar value `1 / k` as the normalized CF2D phase step.  This is
an equality of real coordinates; it does not assert a projection of integer
prime data or any continuum limit.
-/

namespace DkMath.CosmicFormula.Projection

open DkMath.CosmicFormula.Rotation.CF2D

/-- The projection gap at `P = k - 1` equals the CF2D normalized step. -/
theorem projectionGap_eq_regularPhaseStep {k : ℕ} (_hk : 0 < k) :
    U ((k : ℝ) - 1) = regularPhaseStep k := by
  unfold U regularPhaseStep DkMath.Analysis.DkNNRealQ.normalizedCycleStep
  rw [show (k : ℝ) - 1 + 1 = (k : ℝ) by ring]

/-- The projection coordinate plus one is the same CF2D normalized step. -/
theorem projection_add_one_eq_regularPhaseStep {k : ℕ} (hk : 0 < k) :
    Pi ((k : ℝ) - 1) + 1 = regularPhaseStep k := by
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  calc
    Pi ((k : ℝ) - 1) + 1 = U ((k : ℝ) - 1) := by
      apply cosmicProjection_gap_eq
      rw [show (k : ℝ) - 1 + 1 = (k : ℝ) by ring]
      exact hkR
    _ = regularPhaseStep k := projectionGap_eq_regularPhaseStep hk

end DkMath.CosmicFormula.Projection
