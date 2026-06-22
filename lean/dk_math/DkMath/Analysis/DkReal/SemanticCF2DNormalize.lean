/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DPath
import Mathlib.Analysis.SpecialFunctions.Sqrt

#print "file: DkMath.Analysis.DkReal.SemanticCF2DNormalize"

/-!
# Boundary normalization of one affine phase

The affine phase edge is continuous but leaves its initial `q2` boundary by
the exact positive factor `phaseDepth t`. This module removes that scalar
defect:

`normalizedPhaseEdge r z t = (1 / sqrt (phaseDepth t)) * semanticPhaseEdge r z t`.

For a semantic core-zero kernel, the normalized edge has the same `q2` value
as `z` at every real parameter. This is the first boundary-valued continuous
transition, still without a circle, angle, or trigonometric parametrization.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/-- The positive scalar that returns an affine phase point to its `q2` boundary. -/
def phaseNormalization (t : ℝ) : ℝ :=
  1 / Real.sqrt (phaseDepth t)

/-- The square root of phase depth is strictly positive. -/
theorem sqrt_phaseDepth_pos (t : ℝ) :
    0 < Real.sqrt (phaseDepth t) :=
  Real.sqrt_pos.2 (phaseDepth_pos t)

/-- The square root used for normalization never vanishes. -/
theorem sqrt_phaseDepth_ne_zero (t : ℝ) :
    Real.sqrt (phaseDepth t) ≠ 0 :=
  (sqrt_phaseDepth_pos t).ne'

/-- Phase normalization is strictly positive. -/
theorem phaseNormalization_pos (t : ℝ) :
    0 < phaseNormalization t :=
  one_div_pos.mpr (sqrt_phaseDepth_pos t)

/-- The normalization factor begins at one. -/
@[simp]
theorem phaseNormalization_zero :
    phaseNormalization 0 = 1 := by
  simp [phaseNormalization]

/-- The normalization factor ends at one. -/
@[simp]
theorem phaseNormalization_one :
    phaseNormalization 1 = 1 := by
  simp [phaseNormalization]

/-- The normalization factor inherits the midpoint reflection symmetry. -/
@[simp]
theorem phaseNormalization_one_sub (t : ℝ) :
    phaseNormalization (1 - t) = phaseNormalization t := by
  simp [phaseNormalization]

/-- Phase depth is a continuous scalar profile. -/
theorem continuous_phaseDepth :
    Continuous phaseDepth := by
  unfold phaseDepth
  fun_prop

/-- The positive normalization factor varies continuously. -/
theorem continuous_phaseNormalization :
    Continuous phaseNormalization := by
  unfold phaseNormalization
  exact continuous_const.div
    (Real.continuous_sqrt.comp continuous_phaseDepth)
    sqrt_phaseDepth_ne_zero

/--
Scale a CF2D state by the reciprocal square root of affine phase depth.
-/
def normalizedPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    (phaseNormalization t * (semanticPhaseEdge r z t).core)
    (phaseNormalization t * (semanticPhaseEdge r z t).beam)

/-- The normalized edge starts at the original state. -/
@[simp]
theorem normalizedPhaseEdge_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    normalizedPhaseEdge r z 0 = z := by
  cases z
  simp [normalizedPhaseEdge]

/-- The normalized edge ends at the next action state. -/
@[simp]
theorem normalizedPhaseEdge_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    normalizedPhaseEdge r z 1 = semanticAct r z := by
  cases z
  simp [normalizedPhaseEdge, semanticAct, UnitKernel.act, semanticUnitKernel,
    semanticVec, Vec.star]

/--
For a core-zero kernel, normalization restores the original `q2` boundary at
every parameter value.
-/
theorem normalizedPhaseEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (normalizedPhaseEdge r z t) = Vec.q2 z := by
  have hsqrt_sq :
      (Real.sqrt (phaseDepth t)) ^ 2 = phaseDepth t :=
    Real.sq_sqrt (phaseDepth_nonneg t)
  have hsqrt_ne := sqrt_phaseDepth_ne_zero t
  rw [show Vec.q2 (normalizedPhaseEdge r z t) =
      phaseNormalization t ^ 2 * Vec.q2 (semanticPhaseEdge r z t) by
    simp [normalizedPhaseEdge, Vec.q2]
    ring]
  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore]
  unfold phaseNormalization
  field_simp
  rw [hsqrt_sq]

/-- The normalized master edge is continuous. -/
theorem continuous_normalizedPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Continuous (fun t : ℝ => normalizedPhaseEdge r z t) := by
  rcases continuous_vec_iff.mp (continuous_semanticPhaseEdge r z) with
    ⟨hcore, hbeam⟩
  apply Continuous.vec_mk
  · exact continuous_phaseNormalization.mul hcore
  · exact continuous_phaseNormalization.mul hbeam

end

end DkMath.Analysis.DkNNRealQ
