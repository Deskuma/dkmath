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

/-- Squared normalization cancels the affine boundary-depth factor. -/
theorem phaseNormalization_sq_mul_phaseDepth (t : ℝ) :
    phaseNormalization t ^ 2 * phaseDepth t = 1 := by
  have hsqrt_sq :
      (Real.sqrt (phaseDepth t)) ^ 2 = phaseDepth t :=
    Real.sq_sqrt (phaseDepth_nonneg t)
  have hsqrt_ne := sqrt_phaseDepth_ne_zero t
  unfold phaseNormalization
  field_simp
  rw [hsqrt_sq]

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
  rw [show Vec.q2 (normalizedPhaseEdge r z t) =
      phaseNormalization t ^ 2 * Vec.q2 (semanticPhaseEdge r z t) by
    exact Vec.q2_scale _ _]
  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore]
  calc
    phaseNormalization t ^ 2 * (phaseDepth t * Vec.q2 z) =
        (phaseNormalization t ^ 2 * phaseDepth t) * Vec.q2 z := by ring
    _ = Vec.q2 z := by
      rw [phaseNormalization_sq_mul_phaseDepth]
      ring

/-- The normalized master edge is continuous. -/
theorem continuous_normalizedPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Continuous (fun t : ℝ => normalizedPhaseEdge r z t) := by
  rcases continuous_vec_iff.mp (continuous_semanticPhaseEdge r z) with
    ⟨hcore, hbeam⟩
  apply Continuous.vec_mk
  · exact continuous_phaseNormalization.mul hcore
  · exact continuous_phaseNormalization.mul hbeam

/-!
## Four normalized phases

As in the affine layer, all four boundary-valued transitions are generated
from one master edge by action iteration.
-/

/-- The `k`th normalized phase is an action translate of the master edge. -/
def normalizedPhaseEdgeAt
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
  (semanticAct r)^[k] (normalizedPhaseEdge r z t)

/-- The `k`th normalized phase starts at the `k`th action state. -/
@[simp]
theorem normalizedPhaseEdgeAt_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    normalizedPhaseEdgeAt r z k 0 = (semanticAct r)^[k] z := by
  simp [normalizedPhaseEdgeAt]

/-- The `k`th normalized phase ends at the next action state. -/
@[simp]
theorem normalizedPhaseEdgeAt_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    normalizedPhaseEdgeAt r z k 1 = (semanticAct r)^[k + 1] z := by
  rw [normalizedPhaseEdgeAt, normalizedPhaseEdge_one]
  exact (Function.iterate_succ_apply (semanticAct r) k z).symm

/-- Consecutive normalized phases have identical seam points. -/
theorem normalizedPhaseEdgeAt_seam
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    normalizedPhaseEdgeAt r z k 1 =
      normalizedPhaseEdgeAt r z (k + 1) 0 := by
  simp

/-- Every normalized phase stays on the initial square-mass boundary. -/
theorem normalizedPhaseEdgeAt_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    Vec.q2 (normalizedPhaseEdgeAt r z k t) = Vec.q2 z := by
  rw [normalizedPhaseEdgeAt, semanticAct_iterate_q2,
    normalizedPhaseEdge_q2_of_core_eq_zero hcore]

/-- The normalized phase family is periodic with phase index four. -/
theorem normalizedPhaseEdgeAt_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    normalizedPhaseEdgeAt r z (k + 4) t =
      normalizedPhaseEdgeAt r z k t := by
  have hfour :
      (semanticAct r)^[4] = id :=
    (semanticExactActionOrderFour_of_core_eq_zero hcore).1
  rw [normalizedPhaseEdgeAt, normalizedPhaseEdgeAt,
    Function.iterate_add_apply, hfour]
  rfl

/-- Every action-translated normalized edge is continuous. -/
theorem continuous_normalizedPhaseEdgeAt
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => normalizedPhaseEdgeAt r z k t) := by
  induction k with
  | zero =>
      simpa [normalizedPhaseEdgeAt] using continuous_normalizedPhaseEdge r z
  | succ k ih =>
      rw [show (fun t : ℝ => normalizedPhaseEdgeAt r z (k + 1) t) =
          fun t => semanticAct r (normalizedPhaseEdgeAt r z k t) by
        funext t
        simp [normalizedPhaseEdgeAt, Function.iterate_succ_apply']]
      rcases continuous_vec_iff.mp ih with ⟨hcore, hbeam⟩
      apply Continuous.vec_mk
      · exact
          (continuous_const.mul hcore).sub (continuous_const.mul hbeam)
      · exact
          (continuous_const.mul hbeam).add (continuous_const.mul hcore)

/-- The `k`th normalized phase packaged as a Mathlib path. -/
def normalizedPhasePath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Path ((semanticAct r)^[k] z) ((semanticAct r)^[k + 1] z) where
  toFun t := normalizedPhaseEdgeAt r z k t
  continuous_toFun :=
    (continuous_normalizedPhaseEdgeAt r z k).comp continuous_subtype_val
  source' := by simp
  target' := by simp

/-- Four normalized phases concatenated before endpoint identification. -/
def normalizedFourPhasePath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Path z ((semanticAct r)^[4] z) :=
  (((normalizedPhasePath r z 0).trans (normalizedPhasePath r z 1)).trans
    (normalizedPhasePath r z 2)).trans (normalizedPhasePath r z 3)

/--
Core-zero exact order four closes the normalized boundary-valued transition
into a continuous path based at `z`.
-/
def normalizedClosedFourPhasePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) : Path z z := by
  have hclose : (semanticAct r)^[4] z = z := by
    have hfour := (semanticExactActionOrderFour_of_core_eq_zero hcore).1
    rw [hfour]
    rfl
  let p := normalizedFourPhasePath r z
  exact
    { toContinuousMap := p.toContinuousMap
      source' := p.source
      target' := p.target.trans hclose }

end

end DkMath.Analysis.DkNNRealQ
