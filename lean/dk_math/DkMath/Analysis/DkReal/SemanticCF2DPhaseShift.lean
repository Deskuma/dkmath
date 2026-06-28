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
## Finite cyclic index wrappers

The `Fin 4` wrappers give downstream code a finite cyclic index without
choosing a continuous quotient phase parameter.
-/

/-- Cyclic successor on the four finite indices. -/
def finFourSucc (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩

@[simp]
theorem finFourSucc_val (i : Fin 4) :
    (finFourSucc i).val = (i.val + 1) % 4 := rfl

/-- The finite successor sends `0` to `1`. -/
@[simp]
theorem finFourSucc_zero :
    finFourSucc ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
  rfl

/-- The finite successor sends `1` to `2`. -/
@[simp]
theorem finFourSucc_one :
    finFourSucc ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩ := by
  rfl

/-- The finite successor sends `2` to `3`. -/
@[simp]
theorem finFourSucc_two :
    finFourSucc ⟨2, by norm_num⟩ = ⟨3, by norm_num⟩ := by
  rfl

/-- The finite successor sends `3` back to `0`. -/
@[simp]
theorem finFourSucc_three :
    finFourSucc ⟨3, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  rfl

/-- Applying the finite successor four times returns to the starting index. -/
theorem finFourSucc_four_cycle (i : Fin 4) :
    finFourSucc (finFourSucc (finFourSucc (finFourSucc i))) = i := by
  fin_cases i <;> rfl

/-- The shifted base state indexed by `Fin 4`. -/
def shiftedSemanticFinBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
  shiftedSemanticIndexedBase r z i.val

@[simp]
theorem shiftedSemanticFinBase_eq_indexed
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinBase r z i =
      shiftedSemanticIndexedBase r z i.val := rfl

/-- Every finite shifted base remains on the original square-mass level. -/
theorem shiftedSemanticFinBase_q2
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    Vec.q2 (shiftedSemanticFinBase r z i) = Vec.q2 z :=
  shiftedSemanticIndexedBase_q2 r z i.val

/-- The finite shifted base as a point of the original square-mass level set. -/
def shiftedSemanticFinBaseLevelPoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedBaseLevelPoint r z i.val

@[simp]
theorem shiftedSemanticFinBaseLevelPoint_eq_indexed
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinBaseLevelPoint r z i =
      shiftedSemanticIndexedBaseLevelPoint r z i.val := rfl

@[simp]
theorem shiftedSemanticFinBaseLevelPoint_val
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    (shiftedSemanticFinBaseLevelPoint r z i).1 =
      shiftedSemanticFinBase r z i := rfl

/-- The shifted normalized edge indexed by `Fin 4`. -/
def shiftedSemanticFinEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) : Vec ℝ :=
  shiftedSemanticIndexedEdge r z i.val t

@[simp]
theorem shiftedSemanticFinEdge_eq_indexed
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
    shiftedSemanticFinEdge r z i t =
      shiftedSemanticIndexedEdge r z i.val t := rfl

/-- The finite shifted edge starts at its finite left endpoint. -/
theorem shiftedSemanticFinEdge_leftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i 0 =
      shiftedSemanticLeftEndpoint r (shiftedSemanticFinBase r z i) := by
  simp [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge]

/-- The finite shifted edge ends at its finite right endpoint. -/
theorem shiftedSemanticFinEdge_rightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i 1 =
      shiftedSemanticRightEndpoint r (shiftedSemanticFinBase r z i) := by
  simp [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge]

/-- The finite shifted edge stays on the original square-mass boundary. -/
theorem shiftedSemanticFinEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
    Vec.q2 (shiftedSemanticFinEdge r z i t) = Vec.q2 z := by
  rw [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge,
    shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore,
    shiftedSemanticIndexedBase_q2]

/-- The finite shifted edge center reaches the next indexed base state. -/
theorem shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i phaseCenter =
      shiftedSemanticIndexedBase r z (i.val + 1) :=
  shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z i.val

/-- The finite shifted edge center reaches the cyclic successor base. -/
theorem shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i phaseCenter =
      shiftedSemanticFinBase r z (finFourSucc i) := by
  fin_cases i
  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨0, by norm_num⟩
  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨1, by norm_num⟩
  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨2, by norm_num⟩
  · calc
      shiftedSemanticFinEdge r z ⟨3, by norm_num⟩ phaseCenter =
          shiftedSemanticIndexedBase r z (3 + 1) :=
        shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨3, by norm_num⟩
      _ = shiftedSemanticFinBase r z (finFourSucc ⟨3, by norm_num⟩) := by
        norm_num
        exact semanticAct_four_of_core_eq_zero hcore z

/-- The finite shifted normalized edge as a path. -/
def shiftedSemanticFinPath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    Path
      (shiftedSemanticLeftEndpoint r (shiftedSemanticFinBase r z i))
      (shiftedSemanticRightEndpoint r (shiftedSemanticFinBase r z i)) :=
  shiftedSemanticIndexedPath r z i.val

@[simp]
theorem shiftedSemanticFinPath_apply
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticFinPath r z i t =
      shiftedSemanticFinEdge r z i t := rfl

/-- The finite shifted left endpoint inside the original square-mass level set. -/
def shiftedSemanticFinLeftLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedLeftLevelEndpoint hcore z i.val

/-- The finite shifted right endpoint inside the original square-mass level set. -/
def shiftedSemanticFinRightLevelEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedRightLevelEndpoint hcore z i.val

@[simp]
theorem shiftedSemanticFinLeftLevelEndpoint_eq_indexed
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLeftLevelEndpoint hcore z i =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z i.val := rfl

@[simp]
theorem shiftedSemanticFinRightLevelEndpoint_eq_indexed
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinRightLevelEndpoint hcore z i =
      shiftedSemanticIndexedRightLevelEndpoint hcore z i.val := rfl

/-- The finite shifted level edge inside the original square-mass boundary. -/
def shiftedSemanticFinLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedLevelEdge hcore z i.val t

@[simp]
theorem shiftedSemanticFinLevelEdge_eq_indexed
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
    shiftedSemanticFinLevelEdge hcore z i t =
      shiftedSemanticIndexedLevelEdge hcore z i.val t := rfl

@[simp]
theorem shiftedSemanticFinLevelEdge_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
    (shiftedSemanticFinLevelEdge hcore z i t).1 =
      shiftedSemanticFinEdge r z i t := rfl

/-- The finite level edge center reaches the next indexed base level point. -/
theorem shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
      shiftedSemanticIndexedBaseLevelPoint r z (i.val + 1) :=
  shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero hcore z i.val

/-- The finite level edge center reaches the cyclic successor base point. -/
theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
      shiftedSemanticIndexedBaseLevelPoint r z (finFourSucc i).val := by
  fin_cases i
  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨0, by norm_num⟩
  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨1, by norm_num⟩
  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨2, by norm_num⟩
  · apply Subtype.ext
    calc
      (shiftedSemanticFinLevelEdge hcore z ⟨3, by norm_num⟩ phaseCenter).1 =
          shiftedSemanticIndexedBase r z (3 + 1) :=
        congrArg Subtype.val
          (shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero
            hcore z ⟨3, by norm_num⟩)
      _ = (shiftedSemanticIndexedBaseLevelPoint r z (finFourSucc ⟨3, by norm_num⟩).val).1 := by
        norm_num
        exact semanticAct_four_of_core_eq_zero hcore z

/-- The finite level edge center reaches the finite successor base point. -/
theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
      shiftedSemanticFinBaseLevelPoint r z (finFourSucc i) := by
  simpa using
    shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero hcore z i

/-- The finite shifted normalized edge as a fixed-boundary path. -/
def shiftedSemanticFinLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    Path (shiftedSemanticFinLeftLevelEndpoint hcore z i)
      (shiftedSemanticFinRightLevelEndpoint hcore z i) :=
  shiftedSemanticIndexedLevelPath hcore z i.val

@[simp]
theorem shiftedSemanticFinLevelPath_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    (shiftedSemanticFinLevelPath hcore z i t).1 =
      shiftedSemanticFinEdge r z i t := rfl

/-- Applying a finite level path gives the corresponding finite level edge. -/
@[simp]
theorem shiftedSemanticFinLevelPath_apply_eq_levelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticFinLevelPath hcore z i t =
      shiftedSemanticFinLevelEdge hcore z i t := rfl

/--
Finite cyclic seam compatibility: the right endpoint of finite edge `i` is
the left endpoint of its cyclic successor.
-/
theorem shiftedSemanticFinRightLevelEndpoint_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinRightLevelEndpoint hcore z i =
      shiftedSemanticFinLeftLevelEndpoint hcore z (finFourSucc i) := by
  fin_cases i
  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 0
  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 1
  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 2
  · exact shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left hcore z

/-- Finite seam compatibility from edge `0` to edge `1`. -/
theorem shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinRightLevelEndpoint hcore z ⟨0, by norm_num⟩ =
      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨1, by norm_num⟩ :=
  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨0, by norm_num⟩

/-- Finite seam compatibility from edge `1` to edge `2`. -/
theorem shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinRightLevelEndpoint hcore z ⟨1, by norm_num⟩ =
      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨2, by norm_num⟩ :=
  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨1, by norm_num⟩

/-- Finite seam compatibility from edge `2` to edge `3`. -/
theorem shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinRightLevelEndpoint hcore z ⟨2, by norm_num⟩ =
      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨3, by norm_num⟩ :=
  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨2, by norm_num⟩

/-- Finite seam compatibility from edge `3` back to edge `0`. -/
theorem shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinRightLevelEndpoint hcore z ⟨3, by norm_num⟩ =
      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨0, by norm_num⟩ :=
  by
    simpa using
      shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨3, by norm_num⟩

/-- Finite-index alias for the closed four shifted level path. -/
def shiftedSemanticFinFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) :=
  shiftedSemanticFourLevelPath hcore z

/-- Source endpoint of the closed shifted four-level path. -/
theorem shiftedSemanticFourLevelPath_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFourLevelPath hcore z 0 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
  (shiftedSemanticFourLevelPath hcore z).source

/-- Target endpoint of the closed shifted four-level path. -/
theorem shiftedSemanticFourLevelPath_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFourLevelPath hcore z 1 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
  (shiftedSemanticFourLevelPath hcore z).target

/-- Source endpoint of the finite alias for the closed shifted four-level path. -/
theorem shiftedSemanticFinFourLevelPath_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinFourLevelPath hcore z 0 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
  shiftedSemanticFourLevelPath_source hcore z

/-- Target endpoint of the finite alias for the closed shifted four-level path. -/
theorem shiftedSemanticFinFourLevelPath_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinFourLevelPath hcore z 1 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
  shiftedSemanticFourLevelPath_target hcore z

/--
Every point of the finite closed shifted path lies on the original
square-mass boundary.
-/
theorem shiftedSemanticFinFourLevelPath_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 ((shiftedSemanticFinFourLevelPath hcore z t).1) = Vec.q2 z :=
  (shiftedSemanticFinFourLevelPath hcore z t).2

/-!
## Finite chart evaluation and seam quotient

The next definitions expose the finite chart space for the shifted boundary:
a finite edge index together with a local unit-interval parameter. The seam
relation is first recorded directly, then closed under Mathlib's generated
equivalence relation so chart evaluation can descend to a quotient wrapper.
-/

/-- A finite shifted chart is one of four shifted edges and a local parameter. -/
abbrev ShiftedFiniteChart :=
  Fin 4 × unitInterval

/-- Evaluate a finite shifted chart inside the fixed square-mass boundary. -/
def shiftedSemanticFinChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedFiniteChart) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticFinLevelEdge hcore z p.1 p.2

@[simp]
theorem shiftedSemanticFinChartEval_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedFiniteChart) :
    (shiftedSemanticFinChartEval hcore z p).1 =
      shiftedSemanticFinEdge r z p.1 p.2 := rfl

/-- Evaluating a finite chart at local `0` gives its left endpoint. -/
theorem shiftedSemanticFinChartEval_at_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinChartEval hcore z (i, (0 : unitInterval)) =
      shiftedSemanticFinLeftLevelEndpoint hcore z i := by
  apply Subtype.ext
  simp [shiftedSemanticFinChartEval, shiftedSemanticFinLevelEdge,
    shiftedSemanticIndexedLevelEdge, shiftedSemanticIndexedEdge,
    shiftedSemanticFinLeftLevelEndpoint,
    shiftedSemanticIndexedLeftLevelEndpoint]

/-- Evaluating a finite chart at local `1` gives its right endpoint. -/
theorem shiftedSemanticFinChartEval_at_right
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinChartEval hcore z (i, (1 : unitInterval)) =
      shiftedSemanticFinRightLevelEndpoint hcore z i := by
  apply Subtype.ext
  simp [shiftedSemanticFinChartEval, shiftedSemanticFinLevelEdge,
    shiftedSemanticIndexedLevelEdge, shiftedSemanticIndexedEdge,
    shiftedSemanticFinRightLevelEndpoint,
    shiftedSemanticIndexedRightLevelEndpoint]

/--
Finite seam relation between charts.

It relates the right endpoint of edge `i` to the left endpoint of its finite
successor. This is the generating relation for the later chart quotient.
-/
def shiftedFiniteSeamRel (p q : ShiftedFiniteChart) : Prop :=
  ∃ i : Fin 4,
    p = (i, (1 : unitInterval)) ∧
      q = (finFourSucc i, (0 : unitInterval))

/-- The chart evaluation has matching values across a single finite seam. -/
theorem shiftedSemanticFinChartEval_right_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinChartEval hcore z (i, (1 : unitInterval)) =
      shiftedSemanticFinChartEval hcore z
        (finFourSucc i, (0 : unitInterval)) := by
  rw [shiftedSemanticFinChartEval_at_right,
    shiftedSemanticFinChartEval_at_left]
  exact shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z i

/-- Chart evaluation is compatible with the finite seam relation. -/
theorem shiftedSemanticFinChartEval_eq_of_seamRel
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    {p q : ShiftedFiniteChart}
    (hrel : shiftedFiniteSeamRel p q) :
    shiftedSemanticFinChartEval hcore z p =
      shiftedSemanticFinChartEval hcore z q := by
  rcases hrel with ⟨i, hp, hq⟩
  subst hp
  subst hq
  exact shiftedSemanticFinChartEval_right_eq_succ_left hcore z i

/--
Generated equivalence relation of the finite seam relation.

This is the algebraic cyclic identification of endpoint charts. It deliberately
does not add a topology or path structure to the quotient.
-/
def shiftedFiniteChartRel (p q : ShiftedFiniteChart) : Prop :=
  Relation.EqvGen shiftedFiniteSeamRel p q

/-- Setoid generated by the shifted finite seam relation. -/
def shiftedFiniteChartSetoid : Setoid ShiftedFiniteChart :=
  Relation.EqvGen.setoid shiftedFiniteSeamRel

/--
Finite shifted chart quotient by generated seam equivalence.

This is a cyclic chart parameter only in the algebraic sense: seams are
identified, but no quotient topology, path structure, or Euclidean reading is
selected here.
-/
abbrev ShiftedCyclicChart :=
  Quot shiftedFiniteChartSetoid

/-- Constructor alias for representatives of `ShiftedCyclicChart`. -/
def shiftedCyclicChartMk (p : ShiftedFiniteChart) : ShiftedCyclicChart :=
  Quot.mk shiftedFiniteChartSetoid p

/-- The constructor alias is definitionally the quotient representative map. -/
@[simp]
theorem shiftedCyclicChartMk_eq_mk (p : ShiftedFiniteChart) :
    shiftedCyclicChartMk p = Quot.mk shiftedFiniteChartSetoid p := rfl

/-- Left endpoint representative of a finite shifted chart in the quotient. -/
def shiftedCyclicChartLeft (i : Fin 4) : ShiftedCyclicChart :=
  shiftedCyclicChartMk (i, (0 : unitInterval))

/-- Right endpoint representative of a finite shifted chart in the quotient. -/
def shiftedCyclicChartRight (i : Fin 4) : ShiftedCyclicChart :=
  shiftedCyclicChartMk (i, (1 : unitInterval))

/--
The generating seam is an equality inside the shifted cyclic chart quotient.

This is the quotient-side form of the finite seam law: the right endpoint of
edge `i` and the left endpoint of its finite successor are the same cyclic
chart point.
-/
theorem shiftedCyclicChartRight_eq_succ_left (i : Fin 4) :
    shiftedCyclicChartRight i =
      shiftedCyclicChartLeft (finFourSucc i) := by
  apply Quot.sound
  exact Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩

/-- The quotient seam sends finite edge `0` to finite edge `1`. -/
theorem shiftedCyclicChartRight_zero_eq_one_left :
    shiftedCyclicChartRight (0 : Fin 4) =
      shiftedCyclicChartLeft (1 : Fin 4) := by
  simpa using shiftedCyclicChartRight_eq_succ_left ⟨0, by norm_num⟩

/-- The quotient seam sends finite edge `1` to finite edge `2`. -/
theorem shiftedCyclicChartRight_one_eq_two_left :
    shiftedCyclicChartRight (1 : Fin 4) =
      shiftedCyclicChartLeft (2 : Fin 4) := by
  simpa using shiftedCyclicChartRight_eq_succ_left ⟨1, by norm_num⟩

/-- The quotient seam sends finite edge `2` to finite edge `3`. -/
theorem shiftedCyclicChartRight_two_eq_three_left :
    shiftedCyclicChartRight (2 : Fin 4) =
      shiftedCyclicChartLeft (3 : Fin 4) := by
  simpa using shiftedCyclicChartRight_eq_succ_left ⟨2, by norm_num⟩

/-- The quotient seam sends finite edge `3` back to finite edge `0`. -/
theorem shiftedCyclicChartRight_three_eq_zero_left :
    shiftedCyclicChartRight (3 : Fin 4) =
      shiftedCyclicChartLeft (0 : Fin 4) := by
  simpa using shiftedCyclicChartRight_eq_succ_left ⟨3, by norm_num⟩

/--
The representative map into the shifted cyclic chart quotient is continuous.

This uses Mathlib's quotient topology on `Quot`: a subset of the quotient is
open exactly when its preimage along the representative map is open.
-/
theorem continuous_shiftedCyclicChartMk :
    Continuous shiftedCyclicChartMk := by
  simpa [shiftedCyclicChartMk] using
    (continuous_quot_mk :
      Continuous (@Quot.mk ShiftedFiniteChart shiftedFiniteChartSetoid))

/--
Chart evaluation is compatible with the generated seam equivalence.

The proof is pure relation induction: a generating seam is handled by
`shiftedSemanticFinChartEval_eq_of_seamRel`, while reflexive, symmetric, and
transitive closure steps follow from equality.
-/
theorem shiftedSemanticFinChartEval_eq_of_chartRel
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    {p q : ShiftedFiniteChart}
    (hrel : shiftedFiniteChartRel p q) :
    shiftedSemanticFinChartEval hcore z p =
      shiftedSemanticFinChartEval hcore z q := by
  induction hrel with
  | rel _ _ h =>
      exact shiftedSemanticFinChartEval_eq_of_seamRel hcore z h
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/--
Finite chart evaluation is continuous on each fixed finite edge.

The finite index is frozen here, so continuity is inherited from the indexed
level edge after restricting the real parameter to `unitInterval`.
-/
theorem continuous_shiftedSemanticFinChartEval_of_fixed_index
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    Continuous (fun t : unitInterval =>
      shiftedSemanticFinChartEval hcore z (i, t)) := by
  simpa [shiftedSemanticFinChartEval, shiftedSemanticFinLevelEdge]
    using (continuous_shiftedSemanticIndexedLevelEdge hcore z i.val).comp
      continuous_subtype_val

/--
Finite chart evaluation is continuous before quotienting.

The chart domain is `Fin 4 × unitInterval`. Since `Fin 4` is discrete, it is
enough to prove continuity on each fixed finite edge.
-/
theorem continuous_shiftedSemanticFinChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Continuous (fun p : ShiftedFiniteChart =>
      shiftedSemanticFinChartEval hcore z p) := by
  rw [continuous_prod_of_discrete_left]
  intro i
  exact continuous_shiftedSemanticFinChartEval_of_fixed_index hcore z i

/--
Evaluate a seam-quotiented shifted chart inside the fixed square-mass
boundary.

This is the first descended chart evaluation. It uses only the generated seam
equivalence and remains pre-topological.
-/
def shiftedSemanticCyclicChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedCyclicChart) : LevelSet ℝ (Vec.q2 z) :=
  Quot.lift
    (shiftedSemanticFinChartEval hcore z)
    (by
      intro p q hrel
      exact shiftedSemanticFinChartEval_eq_of_chartRel hcore z hrel)
    p

/-- Quotient evaluation computes to finite chart evaluation on representatives. -/
@[simp]
theorem shiftedSemanticCyclicChartEval_mk
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedFiniteChart) :
    shiftedSemanticCyclicChartEval hcore z (Quot.mk _ p) =
      shiftedSemanticFinChartEval hcore z p := rfl

/-- Quotient evaluation at a left endpoint representative. -/
theorem shiftedSemanticCyclicChartEval_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartLeft i) =
      shiftedSemanticFinLeftLevelEndpoint hcore z i := by
  rw [shiftedCyclicChartLeft, shiftedCyclicChartMk_eq_mk,
    shiftedSemanticCyclicChartEval_mk,
    shiftedSemanticFinChartEval_at_left]

/-- Quotient evaluation at a right endpoint representative. -/
theorem shiftedSemanticCyclicChartEval_right
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
      shiftedSemanticFinRightLevelEndpoint hcore z i := by
  rw [shiftedCyclicChartRight, shiftedCyclicChartMk_eq_mk,
    shiftedSemanticCyclicChartEval_mk,
    shiftedSemanticFinChartEval_at_right]

/--
Quotient evaluation has matching values across the quotient seam.

This is the evaluation-side reading of `shiftedCyclicChartRight_eq_succ_left`.
-/
theorem shiftedSemanticCyclicChartEval_right_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
      shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (finFourSucc i)) := by
  rw [shiftedCyclicChartRight_eq_succ_left]

/--
The descended shifted cyclic chart evaluation is continuous.

The proof connects the representative-level continuity with Mathlib's
quotient-lift continuity theorem. The codomain is already the fixed `q2`
boundary, so no extra boundary predicate is needed.
-/
theorem continuous_shiftedSemanticCyclicChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Continuous (fun p : ShiftedCyclicChart =>
      shiftedSemanticCyclicChartEval hcore z p) := by
  simpa [shiftedSemanticCyclicChartEval] using
    (continuous_shiftedSemanticFinChartEval hcore z).quotient_lift
      (fun p q hrel =>
        shiftedSemanticFinChartEval_eq_of_chartRel hcore z hrel)

/--
The quotient chart edge traversing one finite index.

It is the representative path `t ↦ (i, t)` followed by the quotient map. This
is still a path in the chart quotient, not a Euclidean geometric path.
-/
def shiftedCyclicChartEdgePath (i : Fin 4) :
    Path (shiftedCyclicChartLeft i) (shiftedCyclicChartRight i) where
  toFun t := shiftedCyclicChartMk (i, t)
  continuous_toFun := by
    exact continuous_shiftedCyclicChartMk.comp
      (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- Applying the quotient edge path gives its representative chart class. -/
@[simp]
theorem shiftedCyclicChartEdgePath_apply
    (i : Fin 4) (t : unitInterval) :
    shiftedCyclicChartEdgePath i t =
      shiftedCyclicChartMk (i, t) := rfl

/-- The quotient edge path starts at its left endpoint representative. -/
theorem shiftedCyclicChartEdgePath_source (i : Fin 4) :
    shiftedCyclicChartEdgePath i 0 = shiftedCyclicChartLeft i :=
  (shiftedCyclicChartEdgePath i).source

/-- The quotient edge path ends at its right endpoint representative. -/
theorem shiftedCyclicChartEdgePath_target (i : Fin 4) :
    shiftedCyclicChartEdgePath i 1 = shiftedCyclicChartRight i :=
  (shiftedCyclicChartEdgePath i).target

/--
The first four quotient chart edges concatenated into a closed quotient path.

The casts are exactly the quotient seam equalities. No geometric parameter is
introduced; this is only traversal in the glued chart space.
-/
def shiftedCyclicFourPath :
    Path (shiftedCyclicChartLeft (0 : Fin 4))
      (shiftedCyclicChartLeft (0 : Fin 4)) := by
  let p0 := shiftedCyclicChartEdgePath (0 : Fin 4)
  let p1 := shiftedCyclicChartEdgePath (1 : Fin 4)
  let p2 := shiftedCyclicChartEdgePath (2 : Fin 4)
  let p3 := shiftedCyclicChartEdgePath (3 : Fin 4)
  let h01 := shiftedCyclicChartRight_zero_eq_one_left
  let h12 := shiftedCyclicChartRight_one_eq_two_left
  let h23 := shiftedCyclicChartRight_two_eq_three_left
  let h30 := shiftedCyclicChartRight_three_eq_zero_left
  exact
    (((p0.trans (p1.cast h01 rfl)).trans
      (p2.cast h12 rfl)).trans
      (p3.cast h23 rfl)).cast rfl h30.symm

/-- The closed quotient chart path starts at the first finite left endpoint. -/
theorem shiftedCyclicFourPath_source :
    shiftedCyclicFourPath 0 = shiftedCyclicChartLeft (0 : Fin 4) :=
  shiftedCyclicFourPath.source

/-- The closed quotient chart path returns to the first finite left endpoint. -/
theorem shiftedCyclicFourPath_target :
    shiftedCyclicFourPath 1 = shiftedCyclicChartLeft (0 : Fin 4) :=
  shiftedCyclicFourPath.target

/--
Evaluating a quotient edge path recovers the corresponding fixed-boundary
finite level edge.

This is the local comparison between quotient chart traversal and the
semantic boundary observation.
-/
theorem shiftedSemanticCyclicChartEval_edgePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartEdgePath i t) =
      shiftedSemanticFinLevelEdge hcore z i t := by
  rw [shiftedCyclicChartEdgePath_apply, shiftedCyclicChartMk_eq_mk,
    shiftedSemanticCyclicChartEval_mk]
  rfl

/--
Applying a casted path does not change its pointwise value.

This local helper isolates the endpoint-type bookkeeping used when quotient
seams are inserted into `Path.trans` chains.
-/
theorem shiftedPath_cast_apply
    {α : Type _} [TopologicalSpace α]
    {a b c d : α}
    (p : Path a b) (hac : c = a) (hbd : d = b)
    (t : unitInterval) :
    (p.cast hac hbd) t = p t := rfl

/-- The source endpoint of a concatenated path is the source of the first path. -/
theorem shiftedPath_trans_apply_source
    {α : Type _} [TopologicalSpace α]
    {a b c : α}
    (p : Path a b) (q : Path b c) :
    (p.trans q) 0 = p 0 := by
  rw [p.source, (p.trans q).source]

/-- The target endpoint of a concatenated path is the target of the second path. -/
theorem shiftedPath_trans_apply_target
    {α : Type _} [TopologicalSpace α]
    {a b c : α}
    (p : Path a b) (q : Path b c) :
    (p.trans q) 1 = q 1 := by
  rw [q.target, (p.trans q).target]

/--
Edge-zero specialization of quotient-edge evaluation.

This is the first local comparison needed before normalizing the full
four-edge `Path.trans` chain.
-/
theorem shiftedSemanticCyclicChartEval_edgePath_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartEdgePath (0 : Fin 4) t) =
        shiftedSemanticFinLevelEdge hcore z (0 : Fin 4) t :=
  shiftedSemanticCyclicChartEval_edgePath hcore z (0 : Fin 4) t

/--
Observe a single quotient edge inside the fixed square-mass boundary.

Unlike the closed four-edge path, this object contains no nested
`Path.trans`. It is therefore the clean local bridge between quotient chart
traversal and the direct finite level path.
-/
def shiftedSemanticObservedCyclicEdgePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z i)
      (shiftedSemanticFinRightLevelEndpoint hcore z i) where
  toFun t := shiftedSemanticCyclicChartEval hcore z
    (shiftedCyclicChartEdgePath i t)
  continuous_toFun :=
    (continuous_shiftedSemanticCyclicChartEval hcore z).comp
      (shiftedCyclicChartEdgePath i).continuous_toFun
  source' := by
    rw [shiftedCyclicChartEdgePath_source,
      shiftedSemanticCyclicChartEval_left]
  target' := by
    rw [shiftedCyclicChartEdgePath_target,
      shiftedSemanticCyclicChartEval_right]

/-- Evaluating a single observed quotient edge gives the finite level edge. -/
theorem shiftedSemanticObservedCyclicEdgePath_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticObservedCyclicEdgePath hcore z i t =
      shiftedSemanticFinLevelEdge hcore z i t :=
  shiftedSemanticCyclicChartEval_edgePath hcore z i t

/--
The observed single quotient edge is the direct finite fixed-boundary path.

This is the edge-local comparison theorem. The remaining four-edge comparison
is therefore a path-packaging problem about nested `Path.trans` and endpoint
casts, not a semantic mismatch.
-/
theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticObservedCyclicEdgePath hcore z i =
      shiftedSemanticFinLevelPath hcore z i := by
  apply Path.ext
  funext t
  rw [shiftedSemanticObservedCyclicEdgePath_apply]
  rw [shiftedSemanticFinLevelPath_apply_eq_levelEdge]

/--
Canonical four-edge concatenation with explicit seam equalities.

This helper fixes one standard packaging for a closed four-edge traversal.
It is intentionally generic and pre-geometric: it only records how four paths
are glued by endpoint equalities.
-/
def shiftedFourPathConcatWithSeams
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    (p0 : Path a0 b0)
    (p1 : Path a1 b1)
    (p2 : Path a2 b2)
    (p3 : Path a3 b3)
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0) :
    Path a0 a0 :=
  (((p0.trans (p1.cast h01 rfl)).trans
    (p2.cast h12 rfl)).trans
    (p3.cast h23 rfl)).cast rfl h30.symm

/-- The canonical four-edge concatenator starts at its first source. -/
theorem shiftedFourPathConcatWithSeams_source
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    (p0 : Path a0 b0)
    (p1 : Path a1 b1)
    (p2 : Path a2 b2)
    (p3 : Path a3 b3)
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0) :
    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 0 =
      a0 :=
  (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).source

/-- The canonical four-edge concatenator returns to its first source. -/
theorem shiftedFourPathConcatWithSeams_target
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    (p0 : Path a0 b0)
    (p1 : Path a1 b1)
    (p2 : Path a2 b2)
    (p3 : Path a3 b3)
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0) :
    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 1 =
      a0 :=
  (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).target

/--
Congruence for the canonical four-edge concatenator with fixed seams.

Once two edge packages use the same endpoint equalities, equality of the four
component paths is enough to identify the closed concatenations.
-/
theorem shiftedFourPathConcatWithSeams_congr
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    {p0 q0 : Path a0 b0}
    {p1 q1 : Path a1 b1}
    {p2 q2 : Path a2 b2}
    {p3 q3 : Path a3 b3}
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0)
    (hp0 : p0 = q0)
    (hp1 : p1 = q1)
    (hp2 : p2 = q2)
    (hp3 : p3 = q3) :
    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 =
      shiftedFourPathConcatWithSeams q0 q1 q2 q3 h01 h12 h23 h30 := by
  cases hp0
  cases hp1
  cases hp2
  cases hp3
  rfl

/--
Canonical quotient four-edge path via the common seam concatenator.

This is the quotient-chart version of the canonical via-edge packaging used
for semantic observations below.
-/
def shiftedCyclicFourPathViaEdges :
    Path (shiftedCyclicChartLeft (0 : Fin 4))
      (shiftedCyclicChartLeft (0 : Fin 4)) :=
  shiftedFourPathConcatWithSeams
    (shiftedCyclicChartEdgePath (0 : Fin 4))
    (shiftedCyclicChartEdgePath (1 : Fin 4))
    (shiftedCyclicChartEdgePath (2 : Fin 4))
    (shiftedCyclicChartEdgePath (3 : Fin 4))
    shiftedCyclicChartRight_zero_eq_one_left
    shiftedCyclicChartRight_one_eq_two_left
    shiftedCyclicChartRight_two_eq_three_left
    shiftedCyclicChartRight_three_eq_zero_left

/-- The older quotient closed path is definitionally the canonical via-edge path. -/
theorem shiftedCyclicFourPath_eq_viaEdges :
    shiftedCyclicFourPath = shiftedCyclicFourPathViaEdges := rfl

/--
Canonical four-edge path obtained by observing quotient edges individually.

This avoids comparing against the older closed quotient path packaging
directly. The four single-edge observations are first put into one standard
concatenation shape.
-/
def shiftedSemanticObservedCyclicFourPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
  shiftedFourPathConcatWithSeams
    (shiftedSemanticObservedCyclicEdgePath hcore z (0 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath hcore z (1 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath hcore z (2 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath hcore z (3 : Fin 4))
    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)

/--
Canonical four-edge path obtained from direct finite fixed-boundary edges.

It uses the same concatenator and the same seam equalities as the observed
quotient-edge version.
-/
def shiftedSemanticFinFourLevelPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
  shiftedFourPathConcatWithSeams
    (shiftedSemanticFinLevelPath hcore z (0 : Fin 4))
    (shiftedSemanticFinLevelPath hcore z (1 : Fin 4))
    (shiftedSemanticFinLevelPath hcore z (2 : Fin 4))
    (shiftedSemanticFinLevelPath hcore z (3 : Fin 4))
    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)

/--
The older finite four-level path is the canonical direct finite via-edge path.

The `Fin 4` wrappers are thin aliases for the indexed paths and seams used by
the older definition.
-/
theorem shiftedSemanticFinFourLevelPath_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinFourLevelPath hcore z =
      shiftedSemanticFinFourLevelPathViaEdges hcore z := rfl

/--
The canonical observed four-edge path equals the canonical direct finite path.

Because both sides use the same four-path concatenator, the proof reduces to
the four single-edge observed/direct equalities.
-/
theorem shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathViaEdges hcore z =
      shiftedSemanticFinFourLevelPathViaEdges hcore z :=
  shiftedFourPathConcatWithSeams_congr
    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (0 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (1 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (2 : Fin 4))
    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (3 : Fin 4))

/--
The closed quotient chart path observed inside the fixed square-mass boundary.

This composes the closed quotient traversal with the descended semantic
evaluation. The codomain is already `LevelSet ℝ (Vec.q2 z)`, so fixed-boundary
membership is carried by the type.
-/
def shiftedSemanticObservedCyclicFourPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4)))
      (shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4))) where
  toFun t := shiftedSemanticCyclicChartEval hcore z (shiftedCyclicFourPath t)
  continuous_toFun :=
    (continuous_shiftedSemanticCyclicChartEval hcore z).comp
      shiftedCyclicFourPath.continuous_toFun
  source' := by
    rw [shiftedCyclicFourPath_source]
  target' := by
    rw [shiftedCyclicFourPath_target]

/-- The observed closed quotient path starts at the observed first left endpoint. -/
theorem shiftedSemanticObservedCyclicFourPath_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 0 =
      shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4)) :=
  (shiftedSemanticObservedCyclicFourPath hcore z).source

/-- The observed closed quotient path returns to the observed first left endpoint. -/
theorem shiftedSemanticObservedCyclicFourPath_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 1 =
      shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4)) :=
  (shiftedSemanticObservedCyclicFourPath hcore z).target

/-- Evaluation of the first quotient left endpoint agrees with the finite API. -/
theorem shiftedSemanticCyclicChartEval_left_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartLeft (0 : Fin 4)) =
        shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
  shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)

/--
The older observed closed quotient path recast to finite endpoint types.

The path values are unchanged; only the source and target expressions are
relabelled from the observed quotient left endpoint to the finite left
endpoint.
-/
def shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
  (shiftedSemanticObservedCyclicFourPath hcore z).cast
    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm

/-- The recast observed closed path starts at the finite left endpoint. -/
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z 0 =
      shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
  (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z).source

/-- The recast observed closed path returns to the finite left endpoint. -/
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z 1 =
      shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
  (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z).target

/--
Endpoint casting the older observed path does not change its pointwise values.

This is the local bridge that separates endpoint-type bookkeeping from the
later evaluation-concatenation compatibility problem.
-/
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t =
      shiftedSemanticObservedCyclicFourPath hcore z t :=
  shiftedPath_cast_apply
    (shiftedSemanticObservedCyclicFourPath hcore z)
    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
    t

/--
The observed closed quotient path remains on the original `q2` boundary.

This is a projection of the subtype proof carried by the path codomain.
-/
theorem shiftedSemanticObservedCyclicFourPath_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 ((shiftedSemanticObservedCyclicFourPath hcore z t).1) =
      Vec.q2 z :=
  (shiftedSemanticObservedCyclicFourPath hcore z t).2

/--
The observed quotient traversal and the finite four-level path have the same
source value.

This does not identify the whole paths yet; it records that both constructions
start at the same fixed-boundary semantic state.
-/
theorem shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 0 =
      shiftedSemanticFinFourLevelPath hcore z 0 := by
  rw [shiftedSemanticObservedCyclicFourPath_source,
    shiftedSemanticCyclicChartEval_left_zero,
    shiftedSemanticFinFourLevelPath_source]
  rfl

/-- Value-level source comparison for the observed and finite four-level paths. -/
theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedSemanticObservedCyclicFourPath hcore z 0).1 =
      (shiftedSemanticFinFourLevelPath hcore z 0).1 :=
  congrArg Subtype.val
    (shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
      hcore z)

/--
The observed quotient traversal and the finite four-level path have the same
target value.

Both paths close at the initial fixed-boundary semantic state; later full path
comparison can focus only on the interior `Path.trans` parameterization.
-/
theorem shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 1 =
      shiftedSemanticFinFourLevelPath hcore z 1 := by
  rw [shiftedSemanticObservedCyclicFourPath_target,
    shiftedSemanticCyclicChartEval_left_zero,
    shiftedSemanticFinFourLevelPath_target]
  rfl

/-- Value-level target comparison for the observed and finite four-level paths. -/
theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedSemanticObservedCyclicFourPath hcore z 1).1 =
      (shiftedSemanticFinFourLevelPath hcore z 1).1 :=
  congrArg Subtype.val
    (shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
      hcore z)

/--
The quotiented chart evaluation still lands on the original `q2` boundary.

This small observation is useful downstream because consumers of the quotient
do not need to reopen its representative.
-/
theorem shiftedSemanticCyclicChartEval_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedCyclicChart) :
    Vec.q2 ((shiftedSemanticCyclicChartEval hcore z p).1) = Vec.q2 z :=
  (shiftedSemanticCyclicChartEval hcore z p).2

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

[IMPLEMENTED: semantic-cf2d/shifted-fin-four]
The shifted indexed layer now has `Fin 4` wrappers for bases, edges, paths,
fixed-`q2` level edges, and level paths. A finite cyclic successor records the
four-state seam law without introducing a continuous quotient parameter. The
successor has named small-step facts and a four-cycle law, finite edges expose
endpoint and center-to-successor facts, and the closed shifted path exposes
source and target aliases.

[IMPLEMENTED: semantic-cf2d/shifted-fin-observation]
Finite base states are also packaged as fixed-`q2` level points. The finite
level edge center theorem now targets the finite successor base point, and the
finite closed shifted path exposes source, target, and boundary-observation
facts.

[IMPLEMENTED: semantic-cf2d/shifted-finite-chart]
The finite chart space `Fin 4 × unitInterval` evaluates into the fixed `q2`
boundary. Endpoint chart evaluations and seam-relation compatibility are
proved.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-chart]
The finite seam relation is closed under `Relation.EqvGen`, packaged as a
setoid quotient `ShiftedCyclicChart`, and chart evaluation descends to the
quotient as a fixed-`q2` boundary-valued function.
Representative constructor aliases, left and right endpoint representatives,
quotient seam equality, endpoint evaluation theorems, and quotient evaluation
seam compatibility are also exposed.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-topology]
Mathlib's quotient topology on `Quot` is now connected to the shifted cyclic
chart wrapper. The representative map, finite chart evaluation, and descended
quotient evaluation are continuous. The codomain of the descended evaluation
is already the fixed `q2` boundary.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path]
The quotient chart edge path traverses one finite chart representative, and
the first four quotient edge paths concatenate to a closed quotient path by
using the quotient seam equalities. Evaluating one quotient edge recovers the
corresponding fixed-`q2` finite level edge.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-observation]
The closed quotient path is observed through the descended semantic
evaluation as a fixed-`q2` path. Source, target, endpoint-evaluation, and
boundary-observation aliases are exposed.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path-compare-prep]
The observed quotient path and the finite four-level path now have explicit
source and target comparison theorems. A local `Path.cast` pointwise helper
and an edge-zero evaluation wrapper prepare the later full comparison without
forcing `Path.trans` interval-splitting normalization yet.
The source/target comparison is also exposed after `Subtype.val`. A single
observed quotient edge is packaged as a fixed-boundary path and proved equal
to the direct finite fixed-boundary edge path, so the remaining four-edge
comparison is only nested path-packaging normalization.
A canonical four-edge concatenator with explicit seams now packages both the
observed-edge and direct finite-edge versions. These canonical via-edge
closed paths are equal by the four single-edge equalities.
The older quotient closed path is definitionally equal to its canonical
via-edge form, and the older finite fixed-boundary four-level path is
definitionally equal to the canonical direct finite via-edge form.
The older observed closed path can now be endpoint-cast to the same finite
endpoint type, with source, target, and pointwise apply aliases showing that
only endpoint labels changed.

[TODO: semantic-cf2d/shifted-cyclic-path-eval]
Compare evaluation of the closed quotient path with the fixed-`q2` four-level
path after path-trans cast normalization lemmas are available.

[TODO: semantic-cf2d/shifted-cyclic-via-edge-compare]
The quotient-side closed path and finite closed path match their canonical
via-edge versions. The observed quotient path still needs a lemma commuting
descended semantic evaluation with the canonical four-path concatenator, after
endpoint casting from the observed quotient-left endpoint to the finite left
endpoint.

[TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
Develop any additional quotient-space structure only after the descended
continuous evaluation API has downstream consumers.
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
