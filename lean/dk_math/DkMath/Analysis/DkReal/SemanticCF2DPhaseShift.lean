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
## Semantic shifted endpoint candidates

The natural semantic endpoint candidates are the normalized center states of
two neighboring quarter edges. Their raw midpoint is deliberately computed
below instead of being assumed to be the old seam state.
-/

/-- Left semantic endpoint candidate for the shifted frame. -/
def shiftedSemanticLeftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  normalizedPhaseEdge r z phaseCenter

/-- Right semantic endpoint candidate for the shifted frame. -/
def shiftedSemanticRightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  normalizedPhaseEdge r (semanticAct r z) phaseCenter

/-- The old seam state between the neighboring quarter edges. -/
def shiftedSemanticSeam
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  semanticAct r z

/-- The left semantic endpoint candidate remains on the original `q2` boundary. -/
theorem shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticLeftEndpoint r z) = Vec.q2 z := by
  exact normalizedPhaseEdge_q2_of_core_eq_zero hcore z phaseCenter

/-- The right semantic endpoint candidate remains on the original `q2` boundary. -/
theorem shiftedSemanticRightEndpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticRightEndpoint r z) = Vec.q2 z := by
  rw [shiftedSemanticRightEndpoint,
    normalizedPhaseEdge_q2_of_core_eq_zero hcore,
    semanticAct_q2]

/-- The old seam state is on the same `q2` boundary. -/
theorem shiftedSemanticSeam_q2
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticSeam r z) = Vec.q2 z :=
  semanticAct_q2 r z

/-- Core-zero spelling of `shiftedSemanticSeam_q2`, for uniform downstream APIs. -/
theorem shiftedSemanticSeam_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (_hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticSeam r z) = Vec.q2 z :=
  shiftedSemanticSeam_q2 r z

/--
Raw coordinate midpoint between the shifted semantic endpoint candidates.

This is only the uncorrected midpoint. It is useful precisely because it lets
the next theorem state the correction obstruction explicitly.
-/
def shiftedSemanticRawMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  Vec.mk
    (((shiftedSemanticLeftEndpoint r z).core +
        (shiftedSemanticRightEndpoint r z).core) / 2)
    (((shiftedSemanticLeftEndpoint r z).beam +
        (shiftedSemanticRightEndpoint r z).beam) / 2)

/--
Raw affine interpolation between the semantic shifted endpoint candidates.

This helper is intentionally uncorrected. Its center is the raw midpoint,
which still lies at half square-mass depth under the core-zero hypothesis.
-/
def shiftedSemanticRawAffine
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    ((1 - t) * (shiftedSemanticLeftEndpoint r z).core +
      t * (shiftedSemanticRightEndpoint r z).core)
    ((1 - t) * (shiftedSemanticLeftEndpoint r z).beam +
      t * (shiftedSemanticRightEndpoint r z).beam)

/-- The raw semantic shifted affine starts at the left endpoint candidate. -/
@[simp]
theorem shiftedSemanticRawAffine_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticRawAffine r z 0 = shiftedSemanticLeftEndpoint r z := by
  simp [shiftedSemanticRawAffine]

/-- The raw semantic shifted affine ends at the right endpoint candidate. -/
@[simp]
theorem shiftedSemanticRawAffine_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticRawAffine r z 1 = shiftedSemanticRightEndpoint r z := by
  simp [shiftedSemanticRawAffine]

/-- At the local center, the raw semantic shifted affine is its raw midpoint. -/
@[simp]
theorem shiftedSemanticRawAffine_center_eq_rawMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticRawAffine r z phaseCenter =
      shiftedSemanticRawMidpoint r z := by
  simp [shiftedSemanticRawAffine, shiftedSemanticRawMidpoint, phaseCenter]
  constructor <;> ring

/--
For a core-zero action, the raw midpoint of the normalized center candidates
is a scalar multiple of the old seam state.

The scalar is `phaseNormalization phaseCenter / 2`, not definitionally `1`.
This is the concrete obstruction: a final shifted semantic edge needs an
additional correction or projection law before its center can be identified
with the seam state.
-/
theorem shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticRawMidpoint r z =
      Vec.mk
        ((phaseNormalization phaseCenter / 2) * (shiftedSemanticSeam r z).core)
        ((phaseNormalization phaseCenter / 2) * (shiftedSemanticSeam r z).beam) := by
  cases z
  simp [shiftedSemanticRawMidpoint, shiftedSemanticLeftEndpoint,
    shiftedSemanticRightEndpoint, shiftedSemanticSeam, normalizedPhaseEdge,
    semanticPhaseEdge, phaseCenter, semanticAct_of_core_eq_zero hcore]
  constructor <;> ring

/--
The raw shifted midpoint has the square-mass of the seam scaled by
`(phaseNormalization phaseCenter / 2)^2`.

This packages the same obstruction at the boundary-observation level.
-/
theorem shiftedSemanticRawMidpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticRawMidpoint r z) =
      (phaseNormalization phaseCenter / 2) ^ 2 * Vec.q2 z := by
  rw [shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
  rw [Vec.q2_scale, shiftedSemanticSeam_q2]

/--
At the boundary-observation level, the raw midpoint has only half the original
square mass.

This stronger form makes the obstruction explicit: the candidate endpoints
are individually normalized, but their raw midpoint has fallen back to the
same half-depth value as an unnormalized affine center.
-/
theorem shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticRawMidpoint r z) =
      (1 / 2 : ℝ) * Vec.q2 z := by
  rw [shiftedSemanticRawMidpoint_q2_of_core_eq_zero hcore]
  have hfactor : (phaseNormalization phaseCenter / 2) ^ 2 = 1 / 2 := by
    have hcancel := phaseNormalization_sq_mul_phaseDepth phaseCenter
    rw [phaseDepth_center_eq] at hcancel
    nlinarith
  rw [hfactor]

/--
Correct the raw shifted midpoint by the inverse of its seam-scale factor.

This is only a center correction, not a full shifted semantic path.
-/
def shiftedSemanticCorrectedMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  Vec.mk
    ((2 / phaseNormalization phaseCenter) *
      (shiftedSemanticRawMidpoint r z).core)
    ((2 / phaseNormalization phaseCenter) *
      (shiftedSemanticRawMidpoint r z).beam)

/-- The center normalization factor is nonzero. -/
theorem phaseNormalization_center_ne_zero :
    phaseNormalization phaseCenter ≠ 0 :=
  (phaseNormalization_pos phaseCenter).ne'

/-- At the phase center, the square of the normalization factor is two. -/
theorem phaseNormalization_center_sq :
    phaseNormalization phaseCenter ^ 2 = 2 := by
  have hcancel := phaseNormalization_sq_mul_phaseDepth phaseCenter
  rw [phaseDepth_center_eq] at hcancel
  nlinarith

/--
The correction scalar cancels the raw midpoint seam-scale factor.
-/
theorem shiftedSemanticCorrection_mul_rawScale :
    (2 / phaseNormalization phaseCenter) *
        (phaseNormalization phaseCenter / 2) = 1 := by
  field_simp [phaseNormalization_center_ne_zero]

/--
Under the core-zero law, the corrected shifted midpoint is exactly the old
seam state.

This closes the center correction without yet choosing a pointwise correction
law for the whole shifted semantic edge.
-/
theorem shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCorrectedMidpoint r z = shiftedSemanticSeam r z := by
  rw [shiftedSemanticCorrectedMidpoint,
    shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
  cases shiftedSemanticSeam r z
  simp only [Vec.mk.injEq]
  constructor
  · field_simp [phaseNormalization_center_ne_zero]
  · field_simp [phaseNormalization_center_ne_zero]

/-- The corrected shifted midpoint returns to the original `q2` boundary. -/
theorem shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticCorrectedMidpoint r z) = Vec.q2 z := by
  rw [shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero hcore,
    shiftedSemanticSeam_q2]

/--
The raw shifted semantic affine has the same scalar `q2` profile as the
original affine phase edge.

This verifies that the whole shifted edge can use the same pointwise
normalization scalar, not only a special center correction.
-/
theorem shiftedSemanticRawAffine_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticRawAffine r z t) =
      phaseDepth t * Vec.q2 z := by
  cases z
  simp [shiftedSemanticRawAffine, shiftedSemanticLeftEndpoint,
    shiftedSemanticRightEndpoint, normalizedPhaseEdge, semanticPhaseEdge,
    phaseCenter, semanticAct_of_core_eq_zero hcore, Vec.q2, phaseDepth]
  have hsq : phaseNormalization (1 / 2 : ℝ) ^ 2 = 2 := by
    simpa [phaseCenter] using phaseNormalization_center_sq
  ring_nf
  rw [hsq]
  ring

/--
Pointwise normalization of the raw shifted semantic affine.

This is the first full shifted semantic edge candidate. It is still
pre-geometric: the normalization is expressed only through `q2` depth.
-/
def shiftedSemanticNormalizedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).core)
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).beam)

/-- The normalized shifted edge starts at the left endpoint candidate. -/
@[simp]
theorem shiftedSemanticNormalizedEdge_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 0 = shiftedSemanticLeftEndpoint r z := by
  simp [shiftedSemanticNormalizedEdge]

/-- Endpoint spelling for downstream shifted-path code. -/
theorem shiftedSemanticNormalizedEdge_leftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 0 =
      shiftedSemanticLeftEndpoint r z :=
  shiftedSemanticNormalizedEdge_zero r z

/-- The normalized shifted edge ends at the right endpoint candidate. -/
@[simp]
theorem shiftedSemanticNormalizedEdge_one
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 = shiftedSemanticRightEndpoint r z := by
  simp [shiftedSemanticNormalizedEdge]

/-- Endpoint spelling for downstream shifted-path code. -/
theorem shiftedSemanticNormalizedEdge_rightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 =
      shiftedSemanticRightEndpoint r z :=
  shiftedSemanticNormalizedEdge_one r z

/--
Adjacent shifted normalized edges meet at the same normalized center state.

This is the seam-compatibility fact needed before any cyclic concatenation
layer is introduced.
-/
theorem shiftedSemanticNormalizedEdge_right_eq_next_left
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 =
      shiftedSemanticNormalizedEdge r (semanticAct r z) 0 := by
  simp [shiftedSemanticRightEndpoint, shiftedSemanticLeftEndpoint]

/-- The normalized shifted edge stays on the original `q2` boundary. -/
theorem shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticNormalizedEdge r z t) = Vec.q2 z := by
  rw [show Vec.q2 (shiftedSemanticNormalizedEdge r z t) =
      phaseNormalization t ^ 2 * Vec.q2 (shiftedSemanticRawAffine r z t) by
    exact Vec.q2_scale _ _]
  rw [shiftedSemanticRawAffine_q2_of_core_eq_zero hcore]
  calc
    phaseNormalization t ^ 2 * (phaseDepth t * Vec.q2 z) =
        (phaseNormalization t ^ 2 * phaseDepth t) * Vec.q2 z := by ring
    _ = Vec.q2 z := by
      rw [phaseNormalization_sq_mul_phaseDepth]
      ring

/-- At the center, the normalized shifted edge returns to the old seam. -/
theorem shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z phaseCenter =
      shiftedSemanticSeam r z := by
  rw [shiftedSemanticNormalizedEdge, shiftedSemanticRawAffine_center_eq_rawMidpoint,
    shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
  cases shiftedSemanticSeam r z with
  | mk x y =>
  simp only [Vec.mk.injEq]
  constructor
  · calc
      phaseNormalization phaseCenter *
          ((phaseNormalization phaseCenter / 2) * x) =
        (phaseNormalization phaseCenter ^ 2 / 2) * x := by ring
      _ = x := by rw [phaseNormalization_center_sq]; ring
  · calc
      phaseNormalization phaseCenter *
          ((phaseNormalization phaseCenter / 2) * y) =
        (phaseNormalization phaseCenter ^ 2 / 2) * y := by ring
      _ = y := by rw [phaseNormalization_center_sq]; ring

/--
Center-to-seam spelling using the underlying semantic action.

This form is convenient for later cyclic concatenation, where the seam is
usually expressed as the next action state.
-/
theorem shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z phaseCenter =
      semanticAct r z := by
  rw [shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero hcore]
  rfl

/-!
## Shifted normalized paths

The shifted edge has the same analytic shape as the normalized phase edge:
a continuous raw affine interpolation followed by the same positive scalar
normalization. The path API below is still pre-geometric. It records only
endpoint compatibility, seam compatibility, and fixed-`q2` boundary
membership.
-/

/-- The raw shifted affine edge is continuous. -/
theorem continuous_shiftedSemanticRawAffine
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Continuous (fun t : ℝ => shiftedSemanticRawAffine r z t) := by
  apply Continuous.vec_mk
  · fun_prop
  · fun_prop

/-- The shifted normalized edge is continuous. -/
theorem continuous_shiftedSemanticNormalizedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Continuous (fun t : ℝ => shiftedSemanticNormalizedEdge r z t) := by
  rcases continuous_vec_iff.mp
      (continuous_shiftedSemanticRawAffine r z) with
    ⟨hcore, hbeam⟩
  apply Continuous.vec_mk
  · exact continuous_phaseNormalization.mul hcore
  · exact continuous_phaseNormalization.mul hbeam

/--
The shifted normalized edge packaged as a Mathlib path between neighboring
normalized center states.
-/
def shiftedSemanticNormalizedPath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Path (shiftedSemanticLeftEndpoint r z)
      (shiftedSemanticRightEndpoint r z) where
  toFun t := shiftedSemanticNormalizedEdge r z t
  continuous_toFun :=
    (continuous_shiftedSemanticNormalizedEdge r z).comp continuous_subtype_val
  source' := by simp
  target' := by simp

@[simp]
theorem shiftedSemanticNormalizedPath_apply
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticNormalizedPath r z t =
      shiftedSemanticNormalizedEdge r z t := rfl

/-- The shifted normalized path remains on the original `q2` boundary. -/
theorem shiftedSemanticNormalizedPath_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 (shiftedSemanticNormalizedPath r z t) = Vec.q2 z :=
  shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore z t

/-!
## Shifted paths internal to the square-mass boundary

As in the original normalized path layer, the next wrappers strengthen the
codomain from `Vec Real` to the fixed `q2` level set.
-/

/-- The shifted left endpoint as a point of the fixed square-mass level set. -/
def shiftedSemanticLeftLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticLeftEndpoint r z,
    shiftedSemanticLeftEndpoint_q2_of_core_eq_zero hcore z⟩

/-- The shifted right endpoint as a point of the fixed square-mass level set. -/
def shiftedSemanticRightLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticRightEndpoint r z,
    shiftedSemanticRightEndpoint_q2_of_core_eq_zero hcore z⟩

/-- The shifted seam as a point of the fixed square-mass level set. -/
def shiftedSemanticSeamLevelPoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticSeam r z, shiftedSemanticSeam_q2 r z⟩

/--
The shifted normalized edge as a point of the fixed square-mass level set.
-/
def shiftedSemanticNormalizedLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticNormalizedEdge r z t,
    shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore z t⟩

@[simp]
theorem shiftedSemanticNormalizedLevelEdge_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    (shiftedSemanticNormalizedLevelEdge hcore z t).1 =
      shiftedSemanticNormalizedEdge r z t := rfl

/-- The level-set-valued shifted normalized edge is continuous. -/
theorem continuous_shiftedSemanticNormalizedLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Continuous (fun t : ℝ => shiftedSemanticNormalizedLevelEdge hcore z t) :=
  Continuous.subtype_mk (continuous_shiftedSemanticNormalizedEdge r z) _

/--
The shifted normalized edge as a path internal to the fixed square-mass level
set.
-/
def shiftedSemanticNormalizedLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path (shiftedSemanticLeftLevelEndpoint hcore z)
      (shiftedSemanticRightLevelEndpoint hcore z) where
  toFun t := shiftedSemanticNormalizedLevelEdge hcore z t
  continuous_toFun :=
    (continuous_shiftedSemanticNormalizedLevelEdge hcore z).comp
      continuous_subtype_val
  source' := by
    apply Subtype.ext
    simp [shiftedSemanticNormalizedLevelEdge, shiftedSemanticLeftLevelEndpoint]
  target' := by
    apply Subtype.ext
    simp [shiftedSemanticNormalizedLevelEdge, shiftedSemanticRightLevelEndpoint]

@[simp]
theorem shiftedSemanticNormalizedLevelPath_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticNormalizedLevelPath hcore z t).1 =
      shiftedSemanticNormalizedEdge r z t := rfl

/-- At the center, the level-set-valued shifted path reaches the seam point. -/
theorem shiftedSemanticNormalizedLevelEdge_center_eq_seam
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedLevelEdge hcore z phaseCenter =
      shiftedSemanticSeamLevelPoint r z := by
  apply Subtype.ext
  exact shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero hcore z

/-!
## Indexed shifted normalized edges

The next layer moves the shifted edge along the finite action orbit. The
index is still an action count, not a geometric angle parameter.
-/

/-- The base state for the `k`th shifted edge. -/
def shiftedSemanticIndexedBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) : Vec ℝ :=
  semanticActIter r k z

@[simp]
theorem shiftedSemanticIndexedBase_zero
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticIndexedBase r z 0 = z := rfl

@[simp]
theorem shiftedSemanticIndexedBase_succ
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedBase r z (k + 1) =
      semanticAct r (shiftedSemanticIndexedBase r z k) := by
  simp [shiftedSemanticIndexedBase]

/-- Every indexed base remains on the original square-mass level. -/
theorem shiftedSemanticIndexedBase_q2
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Vec.q2 (shiftedSemanticIndexedBase r z k) = Vec.q2 z := by
  rw [shiftedSemanticIndexedBase, semanticActIter, semanticAct_iterate_q2]

/-- The `k`th shifted normalized edge. -/
def shiftedSemanticIndexedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
  shiftedSemanticNormalizedEdge r (shiftedSemanticIndexedBase r z k) t

/-- The `k`th shifted normalized edge as a Mathlib path. -/
def shiftedSemanticIndexedPath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Path
      (shiftedSemanticLeftEndpoint r (shiftedSemanticIndexedBase r z k))
      (shiftedSemanticRightEndpoint r (shiftedSemanticIndexedBase r z k)) :=
  shiftedSemanticNormalizedPath r (shiftedSemanticIndexedBase r z k)

@[simp]
theorem shiftedSemanticIndexedPath_apply
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
    shiftedSemanticIndexedPath r z k t =
      shiftedSemanticIndexedEdge r z k t := rfl

/-- Consecutive indexed shifted edges share their seam endpoint. -/
theorem shiftedSemanticIndexedEdge_right_eq_next_left
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedEdge r z k 1 =
      shiftedSemanticIndexedEdge r z (k + 1) 0 := by
  rw [shiftedSemanticIndexedEdge, shiftedSemanticIndexedEdge,
    shiftedSemanticIndexedBase_succ]
  exact shiftedSemanticNormalizedEdge_right_eq_next_left r
    (shiftedSemanticIndexedBase r z k)

/--
At its center, the `k`th indexed shifted edge reaches the next indexed base
state.
-/
theorem shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedEdge r z k phaseCenter =
      shiftedSemanticIndexedBase r z (k + 1) := by
  simp [shiftedSemanticIndexedEdge,
    shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero hcore]

/-- Core-zero indexed bases repeat after four action steps. -/
theorem shiftedSemanticIndexedBase_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedBase r z (k + 4) =
      shiftedSemanticIndexedBase r z k := by
  exact semanticActIter_add_four_of_core_eq_zero hcore k z

/-- The indexed shifted left endpoints repeat after four action steps. -/
theorem shiftedSemanticIndexedLeftEndpoint_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticLeftEndpoint r
        (shiftedSemanticIndexedBase r z (k + 4)) =
      shiftedSemanticLeftEndpoint r
        (shiftedSemanticIndexedBase r z k) := by
  rw [shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]

/-- The indexed shifted right endpoints repeat after four action steps. -/
theorem shiftedSemanticIndexedRightEndpoint_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticRightEndpoint r
        (shiftedSemanticIndexedBase r z (k + 4)) =
      shiftedSemanticRightEndpoint r
        (shiftedSemanticIndexedBase r z k) := by
  rw [shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]

/-- Indexed shifted edges repeat after four action steps. -/
theorem shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    shiftedSemanticIndexedEdge r z (k + 4) t =
      shiftedSemanticIndexedEdge r z k t := by
  rw [shiftedSemanticIndexedEdge, shiftedSemanticIndexedEdge,
    shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]

/-!
## Indexed shifted paths inside the square-mass boundary

These wrappers keep the codomain fixed at the original `q2 z` level while
the indexed base state moves by the semantic action.
-/

/-- The indexed base as a point of the original square-mass level set. -/
def shiftedSemanticIndexedBaseLevelPoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticIndexedBase r z k,
    shiftedSemanticIndexedBase_q2 r z k⟩

/-- The indexed shifted left endpoint inside the original square-mass level set. -/
def shiftedSemanticIndexedLeftLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticLeftEndpoint r (shiftedSemanticIndexedBase r z k), by
    rw [shiftedSemanticLeftEndpoint_q2_of_core_eq_zero hcore,
      shiftedSemanticIndexedBase_q2]⟩

/-- The indexed shifted right endpoint inside the original square-mass level set. -/
def shiftedSemanticIndexedRightLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticRightEndpoint r (shiftedSemanticIndexedBase r z k), by
    rw [shiftedSemanticRightEndpoint_q2_of_core_eq_zero hcore,
      shiftedSemanticIndexedBase_q2]⟩

/-- The indexed shifted normalized edge inside the original square-mass level set. -/
def shiftedSemanticIndexedLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
  ⟨shiftedSemanticIndexedEdge r z k t, by
    rw [shiftedSemanticIndexedEdge,
      shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore,
      shiftedSemanticIndexedBase_q2]⟩

@[simp]
theorem shiftedSemanticIndexedLevelEdge_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    (shiftedSemanticIndexedLevelEdge hcore z k t).1 =
      shiftedSemanticIndexedEdge r z k t := rfl

/-- The indexed level-set-valued shifted edge is continuous. -/
theorem continuous_shiftedSemanticIndexedLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => shiftedSemanticIndexedLevelEdge hcore z k t) :=
  Continuous.subtype_mk
    (continuous_shiftedSemanticNormalizedEdge r
      (shiftedSemanticIndexedBase r z k)) _

/-- The indexed shifted normalized edge as a fixed-boundary path. -/
def shiftedSemanticIndexedLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    Path (shiftedSemanticIndexedLeftLevelEndpoint hcore z k)
      (shiftedSemanticIndexedRightLevelEndpoint hcore z k) where
  toFun t := shiftedSemanticIndexedLevelEdge hcore z k t
  continuous_toFun :=
    (continuous_shiftedSemanticIndexedLevelEdge hcore z k).comp
      continuous_subtype_val
  source' := by
    apply Subtype.ext
    simp [shiftedSemanticIndexedLevelEdge,
      shiftedSemanticIndexedLeftLevelEndpoint, shiftedSemanticIndexedEdge]
  target' := by
    apply Subtype.ext
    simp [shiftedSemanticIndexedLevelEdge,
      shiftedSemanticIndexedRightLevelEndpoint, shiftedSemanticIndexedEdge]

@[simp]
theorem shiftedSemanticIndexedLevelPath_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
    (shiftedSemanticIndexedLevelPath hcore z k t).1 =
      shiftedSemanticIndexedEdge r z k t := rfl

/-- Consecutive indexed level endpoints are the same seam point. -/
theorem shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z k =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z (k + 1) := by
  apply Subtype.ext
  simp [shiftedSemanticIndexedRightLevelEndpoint,
    shiftedSemanticIndexedLeftLevelEndpoint, shiftedSemanticRightEndpoint,
    shiftedSemanticLeftEndpoint]

/-- The indexed level edge center is the next indexed base point. -/
theorem shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedLevelEdge hcore z k phaseCenter =
      shiftedSemanticIndexedBaseLevelPoint r z (k + 1) := by
  apply Subtype.ext
  exact shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z k

/-!
## Four indexed shifted paths

The four seam facts below expose the endpoint chain needed for concatenation.
The final seam uses the core-zero four-step return law to close edge `3` back
to edge `0`.
-/

/-- Seam compatibility from indexed shifted level path `0` to `1`. -/
theorem shiftedSemanticIndexedLevelEndpoint_0_1
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z 0 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 1 :=
  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 0

/-- Seam compatibility from indexed shifted level path `1` to `2`. -/
theorem shiftedSemanticIndexedLevelEndpoint_1_2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z 1 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 2 :=
  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 1

/-- Seam compatibility from indexed shifted level path `2` to `3`. -/
theorem shiftedSemanticIndexedLevelEndpoint_2_3
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z 2 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 3 :=
  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 2

/-- Indexed shifted left level endpoints repeat after four action steps. -/
theorem shiftedSemanticIndexedLeftLevelEndpoint_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedLeftLevelEndpoint hcore z (k + 4) =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z k := by
  apply Subtype.ext
  exact shiftedSemanticIndexedLeftEndpoint_add_four_of_core_eq_zero hcore z k

/-- Indexed shifted right level endpoints repeat after four action steps. -/
theorem shiftedSemanticIndexedRightLevelEndpoint_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z (k + 4) =
      shiftedSemanticIndexedRightLevelEndpoint hcore z k := by
  apply Subtype.ext
  exact shiftedSemanticIndexedRightEndpoint_add_four_of_core_eq_zero hcore z k

/-- Closing seam compatibility from indexed shifted level path `3` back to `0`. -/
theorem shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z 3 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 := by
  calc
    shiftedSemanticIndexedRightLevelEndpoint hcore z 3 =
        shiftedSemanticIndexedLeftLevelEndpoint hcore z (3 + 1) :=
      shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 3
    _ = shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 := by
      norm_num
      exact shiftedSemanticIndexedLeftLevelEndpoint_add_four_of_core_eq_zero hcore z 0

/-- Indexed level edges repeat after four action steps. -/
theorem shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
    shiftedSemanticIndexedLevelEdge hcore z (k + 4) t =
      shiftedSemanticIndexedLevelEdge hcore z k t := by
  apply Subtype.ext
  exact shiftedSemanticIndexedEdge_add_four_of_core_eq_zero hcore z k t

/--
The four indexed shifted normalized paths concatenated inside the fixed
square-mass boundary.

The intermediate paths are cast only along proved seam equalities; no
geometric angle parameter is used.
-/
def shiftedSemanticFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) := by
  let p0 := shiftedSemanticIndexedLevelPath hcore z 0
  let p1 := shiftedSemanticIndexedLevelPath hcore z 1
  let p2 := shiftedSemanticIndexedLevelPath hcore z 2
  let p3 := shiftedSemanticIndexedLevelPath hcore z 3
  let h01 := shiftedSemanticIndexedLevelEndpoint_0_1 hcore z
  let h12 := shiftedSemanticIndexedLevelEndpoint_1_2 hcore z
  let h23 := shiftedSemanticIndexedLevelEndpoint_2_3 hcore z
  let h30 := shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left hcore z
  exact
    (((p0.trans (p1.cast h01 rfl)).trans
      (p2.cast h12 rfl)).trans
      (p3.cast h23 rfl)).cast rfl h30.symm

/-!
[IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
The shifted semantic edge uses the normalized center states of neighboring
quarter edges as endpoints. Its raw affine form has the same `phaseDepth`
profile as the original affine edge, so the same pointwise normalization
keeps it on the original `q2` boundary and sends its center to the old seam.

[IMPLEMENTED: semantic-cf2d/shifted-semantic-path]
The shifted normalized edge is continuous and is packaged both as a `Vec Real`
path and as a path internal to the fixed `q2` level set. Adjacent shifted
edges share endpoint states, and the center of the shifted edge is the old
seam state under the core-zero action law.

[IMPLEMENTED: semantic-cf2d/shifted-indexed-edge]
The shifted normalized edge is now indexed by semantic action iterates.
Indexed edges have adjacent seam compatibility, centers at the next indexed
base state, four-step return under the core-zero law, and fixed-`q2`
level-set path wrappers.

[IMPLEMENTED: semantic-cf2d/shifted-four-level-path]
The first four indexed shifted normalized level paths are seam-compatible and
concatenate to a closed fixed-`q2` path object. The closing seam uses the
core-zero four-step return law, not any geometric angle reading.

[TODO: semantic-cf2d/shifted-cyclic-quotient]
Introduce a quotient phase parameter only after the four-edge closed path is
stable enough for downstream consumers.
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
