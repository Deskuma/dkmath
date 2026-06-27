/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DNormalize

#print "file: DkMath.Analysis.DkReal.SemanticCF2DPhaseShift"

/-!
# Phase-center shifts before angles

This module proves the scalar endpoint-center-shift structure of the
pre-geometric CF2D phase route.

The key point is that no circle, arc length, angle, or `pi / 4` input is used.
One quarter-edge of the four-state action has normalized width `1 / 4`; its
center is displaced from an endpoint by `1 / 8`. If neighboring edge centers
are used as the new endpoints, the old seam endpoint becomes the new center.

The global quarter coordinates below are unwrapped real representatives. They
are not quotient parameters modulo one; that cyclic wrapping belongs to a
later phase-coordinate layer.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/-!
## Local center of one affine phase

The scalar profile already detects the midpoint as the unique minimum of
`phaseDepth`. The names in this section expose that fact as a stable API for
the shifted-frame layer.
-/

/-- The local center of one affine phase edge. -/
def phaseCenter : ℝ :=
  1 / 2

/-- The displacement from a quarter-edge endpoint to its center in full-cycle units. -/
def phaseHalfQuarterStep : ℝ :=
  1 / 8

/-- Centered local coordinate on one phase edge. -/
def centeredPhaseCoord (t : ℝ) : ℝ :=
  t - phaseCenter

/--
The center of one affine phase is the unique minimum value of the scalar
depth profile.
-/
@[simp]
theorem phaseDepth_center_eq :
    phaseDepth phaseCenter = 1 / 2 := by
  norm_num [phaseCenter, phaseDepth]

/--
The scalar depth profile recognizes the center intrinsically: reaching the
minimum value `1 / 2` is equivalent to being at `phaseCenter`.
-/
theorem phaseDepth_center_unique (t : ℝ) :
    phaseDepth t = 1 / 2 ↔ t = phaseCenter := by
  simpa [phaseCenter] using phaseDepth_eq_half_iff t

/--
The phase-depth profile is symmetric around the local center.

This is the centered form of the existing `t ↦ 1 - t` reflection law and is
the scalar half-fold symmetry used by the shifted-frame construction.
-/
@[simp]
theorem phaseDepth_centered_reflect (s : ℝ) :
    phaseDepth (phaseCenter + s) = phaseDepth (phaseCenter - s) := by
  simp [phaseCenter, phaseDepth]
  ring

/-!
## Unwrapped quarter-cycle coordinates

These coordinates measure the four-state cycle on the real line before
modulo-one wrapping. Keeping them unwrapped makes the endpoint-center theorem
pure arithmetic.
-/

/-- The unwrapped endpoint of the `k`th quarter edge in full-cycle units. -/
def globalQuarterEndpoint (k : ℕ) : ℝ :=
  (k : ℝ) / 4

/-- The unwrapped center of the `k`th quarter edge in full-cycle units. -/
def globalQuarterCenter (k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 2) / 4

/-- The first quarter endpoint is the full-cycle origin. -/
@[simp]
theorem globalQuarterEndpoint_zero :
    globalQuarterEndpoint 0 = 0 := by
  norm_num [globalQuarterEndpoint]

/-- The fourth quarter endpoint is one full unwrapped cycle. -/
@[simp]
theorem globalQuarterEndpoint_four :
    globalQuarterEndpoint 4 = 1 := by
  norm_num [globalQuarterEndpoint]

/--
The center of a quarter edge is obtained from its endpoint by the half-quarter
shift `1 / 8`.
-/
theorem globalQuarterCenter_eq_endpoint_add_halfQuarter (k : ℕ) :
    globalQuarterCenter k = globalQuarterEndpoint k + phaseHalfQuarterStep := by
  simp [globalQuarterCenter, globalQuarterEndpoint, phaseHalfQuarterStep]
  ring

/--
Successive quarter endpoints differ by one quarter of the unwrapped full
cycle.
-/
theorem globalQuarterEndpoint_succ_eq_endpoint_add_quarter (k : ℕ) :
    globalQuarterEndpoint (k + 1) =
      globalQuarterEndpoint k + 1 / 4 := by
  simp [globalQuarterEndpoint]
  ring

/--
Neighboring quarter-edge centers are separated by one full quarter step.

This is still an unwrapped scalar statement, not an assertion about arc
length on a circle.
-/
theorem globalQuarterCenter_succ_sub_center (k : ℕ) :
    globalQuarterCenter (k + 1) - globalQuarterCenter k = 1 / 4 := by
  simp [globalQuarterCenter]
  ring

/--
Additive form of the center-step law, convenient for later shifted-frame
definitions.
-/
theorem globalQuarterCenter_succ_eq_center_add_quarter (k : ℕ) :
    globalQuarterCenter (k + 1) =
      globalQuarterCenter k + 1 / 4 := by
  simp [globalQuarterCenter]
  ring

/--
If adjacent quarter-edge centers are used as the endpoints of a shifted
observation frame, the old seam endpoint becomes the new center.

This is the algebraic core of the endpoint-to-center shift. It produces the
one-eighth phase displacement without using angle language.
-/
theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
      globalQuarterEndpoint (k + 1) := by
  simp [globalQuarterCenter, globalQuarterEndpoint]
  ring

/-!
## Scalar shifted quarter frame

The shifted frame uses the neighboring quarter centers as its endpoints. In
that frame, the old seam endpoint is now the center. This remains scalar
coordinate bookkeeping; no shifted semantic path is introduced yet.
-/

/-- Left endpoint of the shifted quarter frame around the seam after edge `k`. -/
def shiftedQuarterLeftEndpoint (k : ℕ) : ℝ :=
  globalQuarterCenter k

/-- Right endpoint of the shifted quarter frame around the seam after edge `k`. -/
def shiftedQuarterRightEndpoint (k : ℕ) : ℝ :=
  globalQuarterCenter (k + 1)

/-- Center of the shifted quarter frame, namely the old seam endpoint. -/
def shiftedQuarterCenter (k : ℕ) : ℝ :=
  globalQuarterEndpoint (k + 1)

/-- The shifted-frame left endpoint is the old center of quarter edge `k`. -/
@[simp]
theorem shiftedQuarterLeftEndpoint_eq_center (k : ℕ) :
    shiftedQuarterLeftEndpoint k = globalQuarterCenter k := rfl

/-- The shifted-frame right endpoint is the old center of quarter edge `k + 1`. -/
@[simp]
theorem shiftedQuarterRightEndpoint_eq_next_center (k : ℕ) :
    shiftedQuarterRightEndpoint k = globalQuarterCenter (k + 1) := rfl

/-- The shifted-frame center is the old seam endpoint after quarter edge `k`. -/
@[simp]
theorem shiftedQuarterCenter_eq_next_endpoint (k : ℕ) :
    shiftedQuarterCenter k = globalQuarterEndpoint (k + 1) := rfl

/-- The shifted-frame endpoints are separated by one quarter step. -/
theorem shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter (k : ℕ) :
    shiftedQuarterRightEndpoint k =
      shiftedQuarterLeftEndpoint k + 1 / 4 := by
  simp [shiftedQuarterLeftEndpoint, shiftedQuarterRightEndpoint,
    globalQuarterCenter_succ_eq_center_add_quarter]

/-- Difference form of the shifted-frame endpoint separation. -/
theorem shiftedQuarterRightEndpoint_sub_leftEndpoint (k : ℕ) :
    shiftedQuarterRightEndpoint k - shiftedQuarterLeftEndpoint k = 1 / 4 := by
  rw [shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
  ring

/--
The shifted-frame center is the midpoint of its shifted endpoints.

This is the named scalar reading of the endpoint-to-center shift: the seam
that was an endpoint in the old quarter frame is the center in the shifted
frame.
-/
theorem shiftedQuarterCenter_eq_midpoint (k : ℕ) :
    shiftedQuarterCenter k =
      (shiftedQuarterLeftEndpoint k + shiftedQuarterRightEndpoint k) / 2 := by
  rw [shiftedQuarterCenter_eq_next_endpoint,
    shiftedQuarterLeftEndpoint_eq_center,
    shiftedQuarterRightEndpoint_eq_next_center]
  exact (globalQuarterEndpoint_succ_is_center_between_centers k).symm

/-- The shifted-frame center is a half-quarter step after its left endpoint. -/
theorem shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter (k : ℕ) :
    shiftedQuarterCenter k =
      shiftedQuarterLeftEndpoint k + phaseHalfQuarterStep := by
  rw [shiftedQuarterCenter_eq_midpoint,
    shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
  simp [phaseHalfQuarterStep]
  ring

/-- The shifted-frame right endpoint is a half-quarter step after its center. -/
theorem shiftedQuarterRightEndpoint_eq_center_add_halfQuarter (k : ℕ) :
    shiftedQuarterRightEndpoint k =
      shiftedQuarterCenter k + phaseHalfQuarterStep := by
  rw [shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter,
    shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
  simp [phaseHalfQuarterStep]
  ring

/--
Affine interpolation between the endpoints of the shifted scalar frame.

This is a scalar parameter skeleton only. It does not yet choose semantic
states for a shifted path.
-/
def shiftedQuarterAffine (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t) * shiftedQuarterLeftEndpoint k +
    t * shiftedQuarterRightEndpoint k

/-- The shifted affine scalar starts at its left endpoint. -/
@[simp]
theorem shiftedQuarterAffine_zero_eq_leftEndpoint (k : ℕ) :
    shiftedQuarterAffine k 0 = shiftedQuarterLeftEndpoint k := by
  simp [shiftedQuarterAffine]

/-- The shifted affine scalar ends at its right endpoint. -/
@[simp]
theorem shiftedQuarterAffine_one_eq_rightEndpoint (k : ℕ) :
    shiftedQuarterAffine k 1 = shiftedQuarterRightEndpoint k := by
  simp [shiftedQuarterAffine]

/--
Affine interpolation in the shifted scalar frame reaches the shifted center
at the local phase center.

This prepares a future shifted semantic edge without defining that path yet.
-/
theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
    shiftedQuarterAffine k phaseCenter = shiftedQuarterCenter k := by
  unfold shiftedQuarterAffine
  rw [shiftedQuarterCenter_eq_midpoint]
  simp [phaseCenter]
  ring

/-!
[TODO: semantic-cf2d/shifted-semantic-edge]
Define a shifted semantic edge only after choosing the endpoint states and
the correction law that correspond to `shiftedQuarterLeftEndpoint` and
`shiftedQuarterRightEndpoint`. The natural endpoint candidates are the
normalized center states of neighboring quarter edges, but their raw affine
midpoint is not the old seam state in general; a shifted normalization or
projection law must be selected first. The expected compatibility theorem is
that the selected shifted edge at `phaseCenter` represents
`shiftedQuarterCenter`.
-/

/-!
## Scalar return laws for normalized cycle divisions

The next facts record return counts for a normalized cycle parameter. They do
not state that the path is a Euclidean circle or that the parameter is arc
length.
-/

/-- One step of a positive `k`-division of the normalized cycle. -/
def normalizedCycleStep (k : ℕ) : ℝ :=
  1 / (k : ℝ)

/-- The dyadic cycle step at refinement depth `n`. -/
def dyadicCycleStep (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n

/-- A positive `k`-division returns after `k` scalar steps. -/
theorem normalizedCycleStep_mul_returnCount {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * normalizedCycleStep k = 1 := by
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [normalizedCycleStep, hk_ne]

/-- The dyadic refinement step returns after `2^n` scalar steps. -/
theorem dyadicCycleStep_mul_returnCount (n : ℕ) :
    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1 := by
  have hpow_ne : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  simp [dyadicCycleStep, hpow_ne]

/-!
## Midpoint facts lifted to semantic edges

The scalar center is now connected back to the affine edge and its normalized
boundary-valued form.
-/

/-- At the phase center, the master affine edge is the coordinatewise average of its endpoints. -/
theorem semanticPhaseEdge_center
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticPhaseEdge r z phaseCenter =
      Vec.mk
        ((z.core + (semanticAct r z).core) / 2)
        ((z.beam + (semanticAct r z).beam) / 2) := by
  cases z
  simp [semanticPhaseEdge, phaseCenter]
  constructor <;> ring

/--
Under the core-zero action law, the affine midpoint has exactly half the
initial `q2` depth.
-/
theorem semanticPhaseEdge_q2_center_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (semanticPhaseEdge r z phaseCenter) =
      (1 / 2 : ℝ) * Vec.q2 z := by
  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore, phaseDepth_center_eq]

/--
At the center, normalization returns the affine midpoint to the original
`q2` boundary.
-/
theorem normalizedPhaseEdge_q2_center_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (normalizedPhaseEdge r z phaseCenter) = Vec.q2 z :=
  normalizedPhaseEdge_q2_of_core_eq_zero hcore z phaseCenter

end

end DkMath.Analysis.DkNNRealQ
