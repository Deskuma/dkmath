/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DPhase
import DkMath.CosmicFormula.Rotation.CF2D.Topology
import Mathlib.Topology.Path

#print "file: DkMath.Analysis.DkReal.SemanticCF2DPath"

/-!
# Continuous four-phase path

This module packages the affine phase edges as Mathlib paths and concatenates
four of them. The result is a continuous closed piecewise-affine loop.

It is not yet a path on a fixed `q2` boundary. Boundary normalization remains
a separate analytic construction.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D
open unitInterval

noncomputable section

/-- The unrestricted real-parameter master edge is continuous. -/
theorem continuous_semanticPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Continuous (fun t : ℝ => semanticPhaseEdge r z t) := by
  apply Continuous.vec_mk
  · fun_prop
  · fun_prop

/-- Every action-translated affine edge is continuous. -/
theorem continuous_semanticPhaseEdgeAt
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => semanticPhaseEdgeAt r z k t) := by
  induction k with
  | zero =>
      simpa [semanticPhaseEdgeAt] using continuous_semanticPhaseEdge r z
  | succ k ih =>
      rw [show (fun t : ℝ => semanticPhaseEdgeAt r z (k + 1) t) =
          fun t => semanticAct r (semanticPhaseEdgeAt r z k t) by
        funext t
        simp [semanticPhaseEdgeAt, Function.iterate_succ_apply']]
      rcases continuous_vec_iff.mp ih with ⟨hcore, hbeam⟩
      apply Continuous.vec_mk
      · exact
          (continuous_const.mul hcore).sub (continuous_const.mul hbeam)
      · exact
          (continuous_const.mul hbeam).add (continuous_const.mul hcore)

/--
The `k`th affine phase restricted to the unit interval, with its endpoints
recorded in the path type.
-/
def semanticPhasePath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Path ((semanticAct r)^[k] z) ((semanticAct r)^[k + 1] z) where
  toFun t := semanticPhaseEdgeAt r z k t
  continuous_toFun :=
    (continuous_semanticPhaseEdgeAt r z k).comp continuous_subtype_val
  source' := by simp
  target' := by simp

@[simp]
theorem semanticPhasePath_apply
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
    semanticPhasePath r z k t = semanticPhaseEdgeAt r z k t := rfl

/--
The four affine phases concatenated in their action order.

The endpoint is initially written as the fourth action iterate. Exact
order four closes it back to the initial state.
-/
def semanticFourPhasePath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Path z ((semanticAct r)^[4] z) :=
  (((semanticPhasePath r z 0).trans (semanticPhasePath r z 1)).trans
    (semanticPhasePath r z 2)).trans (semanticPhasePath r z 3)

/--
For a core-zero kernel, the four concatenated affine phases form a closed
continuous path based at `z`.
-/
def semanticClosedFourPhasePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) : Path z z := by
  have hclose : (semanticAct r)^[4] z = z := by
    have hfour := (semanticExactActionOrderFour_of_core_eq_zero hcore).1
    rw [hfour]
    rfl
  let p := semanticFourPhasePath r z
  exact
    { toContinuousMap := p.toContinuousMap
      source' := p.source
      target' := p.target.trans hclose }

end

end DkMath.Analysis.DkNNRealQ
