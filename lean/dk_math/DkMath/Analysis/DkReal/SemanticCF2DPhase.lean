/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2D

#print "file: DkMath.Analysis.DkReal.SemanticCF2DPhase"

/-!
# Affine phase transitions before circles and angles

This module fills one step of the exact-order-four semantic action by an
affine transition. It deliberately studies the transition before imposing a
circle, an angle coordinate, or trigonometric functions.

The affine edge does not remain on a fixed `q2` boundary. Its departure is
instead measured exactly by

`phaseDepth t = (1 - t)^2 + t^2`.

This scalar profile is symmetric under `t ↦ 1 - t` and reaches its unique
minimum at the midpoint. Thus the first continuous symmetry extracted from
the four-state action is a reflection symmetry of boundary depth, rather than
an assumed symmetry of a Euclidean circle.

The profile is also the intended observation point for later refinement and
normalization experiments. Any connection with Gaussian weights or a
normalization constant must be proved in a separate limit layer; it is not
assumed by the affine construction here.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/-!
## The scalar half-fold profile

Square completion exposes the midpoint reflection and the positive lower
bound without geometric terminology.
-/

/--
The relative `q2` depth of the affine transition between two consecutive
core-zero action states.
-/
def phaseDepth (t : ℝ) : ℝ :=
  (1 - t) ^ 2 + t ^ 2

/-- Square completion centers the phase depth at the half transition. -/
theorem phaseDepth_eq_two_sq_add_half (t : ℝ) :
    phaseDepth t = 2 * (t - (1 / 2 : ℝ)) ^ 2 + 1 / 2 := by
  simp [phaseDepth]
  ring

/-- The phase depth is bounded below by one half. -/
theorem one_half_le_phaseDepth (t : ℝ) :
    (1 / 2 : ℝ) ≤ phaseDepth t := by
  rw [phaseDepth_eq_two_sq_add_half]
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]

/-- In particular, affine phase depth never vanishes. -/
theorem phaseDepth_pos (t : ℝ) :
    0 < phaseDepth t :=
  lt_of_lt_of_le (by norm_num) (one_half_le_phaseDepth t)

/-- Phase depth is nonnegative. -/
theorem phaseDepth_nonneg (t : ℝ) :
    0 ≤ phaseDepth t :=
  (phaseDepth_pos t).le

/--
The inward depth is reflected about the midpoint of a transition.

This is the first continuous half-fold symmetry obtained from the discrete
four-state action.
-/
@[simp]
theorem phaseDepth_one_sub (t : ℝ) :
    phaseDepth (1 - t) = phaseDepth t := by
  simp [phaseDepth]
  ring

/-- The affine transition begins on the original `q2` boundary. -/
@[simp]
theorem phaseDepth_zero :
    phaseDepth 0 = 1 := by
  norm_num [phaseDepth]

/-- The affine transition ends on the next copy of the same boundary. -/
@[simp]
theorem phaseDepth_one :
    phaseDepth 1 = 1 := by
  norm_num [phaseDepth]

/-- The midpoint is the deepest point of the affine transition. -/
@[simp]
theorem phaseDepth_half :
    phaseDepth (1 / 2 : ℝ) = 1 / 2 := by
  norm_num [phaseDepth]

/-!
## One affine master edge

All later phase edges are intended to be action translates of this one
formula. The definition remains coordinatewise so that no additional module
structure is imposed on `Vec`.
-/

/--
The affine transition from `z` to its next semantic action state.

The parameter is an unrestricted real number. Restriction to the unit
interval belongs to the later topological path wrapper.
-/
def semanticPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    ((1 - t) * z.core + t * (semanticAct r z).core)
    ((1 - t) * z.beam + t * (semanticAct r z).beam)

/-- Coordinate formula for the core component of the master edge. -/
@[simp]
theorem semanticPhaseEdge_core
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) :
    (semanticPhaseEdge r z t).core =
      (1 - t) * z.core + t * (semanticAct r z).core := rfl

/-- Coordinate formula for the beam component of the master edge. -/
@[simp]
theorem semanticPhaseEdge_beam
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) :
    (semanticPhaseEdge r z t).beam =
      (1 - t) * z.beam + t * (semanticAct r z).beam := rfl

/-- The master edge starts at its input state. -/
@[simp]
theorem semanticPhaseEdge_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticPhaseEdge r z 0 = z := by
  cases z
  simp [semanticPhaseEdge]

/-- The master edge ends at the next action state. -/
@[simp]
theorem semanticPhaseEdge_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticPhaseEdge r z 1 = semanticAct r z := by
  cases z
  simp [semanticPhaseEdge, semanticAct, UnitKernel.act, semanticUnitKernel,
    semanticVec, Vec.star]

/--
For a core-zero kernel, the complete departure from the conserved `q2`
boundary is the scalar factor `phaseDepth`.

No circle or angle is used: the cross terms cancel solely because the
boundary action sends `(x,y)` to `(-y,x)`.
-/
theorem semanticPhaseEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (semanticPhaseEdge r z t) =
      phaseDepth t * Vec.q2 z := by
  unfold semanticPhaseEdge
  rw [semanticAct_of_core_eq_zero hcore]
  cases z with
  | mk x y =>
      simp [phaseDepth, Vec.q2]
      ring

/--
The `q2` observation of the second half of an affine transition is the
reflection of the first half.

The state-valued edge is not claimed to be fixed by this reflection; the
symmetry belongs to its scalar boundary-depth observation.
-/
theorem semanticPhaseEdge_q2_one_sub_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (semanticPhaseEdge r z (1 - t)) =
      Vec.q2 (semanticPhaseEdge r z t) := by
  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore,
    semanticPhaseEdge_q2_of_core_eq_zero hcore, phaseDepth_one_sub]

/-!
## One pattern transported through four phases

The phase index does not select one of four separately written formulas.
Instead it transports the single master edge by an iterate of the action.
This is the formal content of “one pattern, turned four times.”
-/

/--
The `k`th affine phase is the `k`-fold action translate of the master edge.
-/
def semanticPhaseEdgeAt
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
  (semanticAct r)^[k] (semanticPhaseEdge r z t)

/-- The `k`th translated edge starts at the `k`th discrete action state. -/
@[simp]
theorem semanticPhaseEdgeAt_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    semanticPhaseEdgeAt r z k 0 = (semanticAct r)^[k] z := by
  simp [semanticPhaseEdgeAt]

/-- The `k`th translated edge ends at the next discrete action state. -/
@[simp]
theorem semanticPhaseEdgeAt_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    semanticPhaseEdgeAt r z k 1 = (semanticAct r)^[k + 1] z := by
  rw [semanticPhaseEdgeAt, semanticPhaseEdge_one]
  exact (Function.iterate_succ_apply (semanticAct r) k z).symm

/--
Adjacent translated edges meet at exactly the same state.

This seam law is obtained from iteration alone; it does not require a
topological quotient or a circular parameter.
-/
theorem semanticPhaseEdgeAt_seam
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    semanticPhaseEdgeAt r z k 1 =
      semanticPhaseEdgeAt r z (k + 1) 0 := by
  simp

/-- Every translated edge has the same `q2` profile as the master edge. -/
theorem semanticPhaseEdgeAt_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    Vec.q2 (semanticPhaseEdgeAt r z k t) =
      phaseDepth t * Vec.q2 z := by
  rw [semanticPhaseEdgeAt, semanticAct_iterate_q2,
    semanticPhaseEdge_q2_of_core_eq_zero hcore]

/--
Core-zero exact order four makes the translated-edge family periodic in its
phase index.
-/
theorem semanticPhaseEdgeAt_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    semanticPhaseEdgeAt r z (k + 4) t =
      semanticPhaseEdgeAt r z k t := by
  have hfour :
      (semanticAct r)^[4] = id :=
    (semanticExactActionOrderFour_of_core_eq_zero hcore).1
  rw [semanticPhaseEdgeAt, semanticPhaseEdgeAt,
    Function.iterate_add_apply, hfour]
  rfl

end

end DkMath.Analysis.DkNNRealQ
