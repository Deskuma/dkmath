# Design 104: Phase-Center Shift Before Angles

## Purpose

This note fixes the next design target for the DkMath trigonometric route.
The goal is to prove the endpoint-center-pole-shift structure before using
circle, arc, angle, or `45 degree` language as formal input.

The intended order is:

```text
four-state action
  -> affine edge filling
  -> center and depth extremum on one edge
  -> shifted observation frame
  -> one-eighth phase displacement
  -> dyadic refinement of the normalized cycle
  -> general k-division observation
  -> later Euclidean reading as theta = pi / 4
```

The one-eighth displacement is the formal object to build first. The Euclidean
angle is only a later interpretation.

## Current Formal Base

The current Lean base already proves the local scalar profile of one affine
transition:

```text
phaseDepth t = (1 - t)^2 + t^2
phaseDepth t = 2 * (t - 1/2)^2 + 1/2
phaseDepth 0 = 1
phaseDepth 1 = 1
phaseDepth (1/2) = 1/2
phaseDepth t = 1/2 iff t = 1/2
phaseDepth (1 - t) = phaseDepth t
```

Relevant theorem names:

```text
phaseDepth_eq_two_sq_add_half
one_half_le_phaseDepth
phaseDepth_zero
phaseDepth_one
phaseDepth_half
phaseDepth_eq_half_iff
phaseDepth_one_sub
```

The normalized edge layer already removes the scalar depth factor:

```text
phaseNormalization t = 1 / sqrt (phaseDepth t)
phaseNormalization 0 = 1
phaseNormalization 1 = 1
phaseNormalization (1 - t) = phaseNormalization t
phaseNormalization t ^ 2 * phaseDepth t = 1
```

Thus the local midpoint is already available as a distinguished point of the
depth profile. What remains is to expose the shifted-frame theorem.

## Vocabulary

Use the following vocabulary in theorem names and docstrings.

```text
endpoint
  the boundary state of one affine transition, represented by t = 0 or t = 1

center
  the local half-transition point t = 1/2

pole
  the distinguished scalar observation point where phaseDepth reaches its
  unique minimum and phaseNormalization reaches its strongest correction

shift
  a change of observation frame in which neighboring centers become the new
  endpoints, and the old seam endpoint becomes the new center
```

The word `pole` is observational here. It is not a singularity of
`phaseDepth`; in fact `phaseDepth` is strictly positive everywhere. It names
the special point selected by the scalar profile.

## Core Shift Principle

For one phase edge, the midpoint is:

```text
center(t in [0,1]) = 1/2
```

For the four-state cyclic action, one edge is one quarter of the full cycle.
If the full cycle is measured by unit length, then edge `k` occupies:

```text
[k/4, (k+1)/4]
```

Its center is:

```text
(k + 1/2) / 4 = k/4 + 1/8
```

The next edge center is:

```text
(k + 3/2) / 4 = (k+1)/4 + 1/8
```

The seam endpoint between the two edges is:

```text
(k + 1) / 4
```

The key shifted-frame identity is:

```text
(((k + 1/2) / 4) + ((k + 3/2) / 4)) / 2 = (k + 1) / 4
```

Interpretation:

```text
old frame:
  seam = endpoint between edge k and edge k+1

shifted frame:
  neighboring centers are the endpoints
  the old seam is the center
```

This is the precise algebraic version of "the endpoint shifts to the center".
It also isolates the half-quarter displacement:

```text
one quarter step = 1/4 of the full cycle
half of one quarter step = 1/8 of the full cycle
```

The later Euclidean interpretation reads this displacement as the motion
corresponding to `theta = pi / 4`, but the formal proof should first use only
`1/8` phase language.

## Refinement Beyond One Eighth

The one-eighth displacement is not an isolated endpoint. It is the first
visible refinement step after the four-state table.

```text
four-state cycle:
  one edge has width 1/4

endpoint-to-center shift:
  half of that edge has width 1/8

repeat the midpoint observation:
  1/8 -> 1/16 -> 1/32 -> ...
```

Thus the same operation suggests the dyadic chain:

```text
1/4 -> 1/8 -> 1/16 -> 1/32 -> ... -> 1/2^n
```

This is not yet an angle subdivision. It is a refinement of the normalized
cycle parameter carried by the conserved boundary mechanism.

For a dyadic step size,

```text
step size = 1 / 2^n
return count = 2^n
```

the return law is the scalar identity:

```text
2^n * (1 / 2^n) = 1
```

This records a finite return count on the normalized cycle. It does not assert
that the path is a Euclidean circle or that the subdivision is arc length.

## General k-Division Observation

The same design can be stated for an arbitrary positive division count `k`.

```text
unit phase step = 1 / k
return count = k
cycle law = k * (1 / k) = 1
```

This gives the parameter skeleton needed by the continuous trigonometric
program:

```text
conserved kernel
  -> normalized cycle
  -> k-division observation
  -> finite return law
  -> refinement / limiting parameter
  -> Euclidean reading
```

The shape of the path is intentionally not part of this theorem. The current
object of study is the periodic parameter and its return law.

## Radius-Like Data

No separate radius should be introduced at this stage. The radius-like datum is
the conserved `q2` level:

```text
q2(z) = constant
```

The phase-like datum is the normalized cyclic parameter. Later Euclidean
geometry may read a fixed `q2` level as a circle of fixed radius, but the
DkMath construction should first prove preservation on the boundary detector.

## Proposed Lean Surface

The scalar names can live near `SemanticCF2DPhase.lean`:

```lean
def phaseCenter : ℝ := 1 / 2
def phaseHalfQuarterStep : ℝ := 1 / 8

def centeredPhaseCoord (t : ℝ) : ℝ :=
  t - phaseCenter
```

The four-edge/global parameter names can live in a small new module, for
example `SemanticCF2DPhaseShift.lean`. These are unwrapped real
representatives; modulo-one cyclic wrapping is a later quotient reading:

```lean
def globalQuarterEndpoint (k : ℕ) : ℝ :=
  (k : ℝ) / 4

def globalQuarterCenter (k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 2) / 4
```

The normalized cycle division names can live in the same module or in a later
small `SemanticCF2DCycle.lean` module:

```lean
def normalizedCycleStep (k : ℕ) : ℝ :=
  1 / (k : ℝ)

def dyadicCycleStep (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n
```

Candidate theorem names:

```lean
theorem phaseDepth_center_eq :
    phaseDepth phaseCenter = 1 / 2

theorem phaseDepth_center_unique (t : ℝ) :
    phaseDepth t = 1 / 2 ↔ t = phaseCenter

theorem phaseDepth_centered_reflect (s : ℝ) :
    phaseDepth (phaseCenter + s) = phaseDepth (phaseCenter - s)

theorem globalQuarterCenter_eq_endpoint_add_halfQuarter (k : ℕ) :
    globalQuarterCenter k = globalQuarterEndpoint k + phaseHalfQuarterStep

theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
      globalQuarterEndpoint (k + 1)

theorem normalizedCycleStep_mul_returnCount {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * normalizedCycleStep k = 1

theorem dyadicCycleStep_mul_returnCount (n : ℕ) :
    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1
```

The theorem `globalQuarterEndpoint_succ_is_center_between_centers` is the main
shift checkpoint. It says that, after shifting the observation frame from
endpoints to neighboring centers, the old endpoint is now the midpoint.

The cycle-step theorems are deliberately scalar. They record return laws for
the normalized parameter before any geometric shape is assigned to the path.

Implemented checkpoint:

```text
SemanticCF2DPhaseShift.lean
  phaseCenter
  phaseHalfQuarterStep
  centeredPhaseCoord
  phaseDepth_center_eq
  phaseDepth_center_unique
  phaseDepth_centered_reflect
  globalQuarterEndpoint
  globalQuarterCenter
  globalQuarterEndpoint_zero
  globalQuarterEndpoint_four
  globalQuarterCenter_eq_endpoint_add_halfQuarter
  globalQuarterEndpoint_succ_eq_endpoint_add_quarter
  globalQuarterCenter_succ_sub_center
  globalQuarterCenter_succ_eq_center_add_quarter
  globalQuarterEndpoint_succ_is_center_between_centers
  shiftedQuarterLeftEndpoint
  shiftedQuarterRightEndpoint
  shiftedQuarterCenter
  shiftedQuarterLeftEndpoint_eq_center
  shiftedQuarterRightEndpoint_eq_next_center
  shiftedQuarterCenter_eq_next_endpoint
  shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter
  shiftedQuarterRightEndpoint_sub_leftEndpoint
  shiftedQuarterCenter_eq_midpoint
  shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter
  shiftedQuarterRightEndpoint_eq_center_add_halfQuarter
  shiftedQuarterAffine
  shiftedQuarterAffine_zero_eq_leftEndpoint
  shiftedQuarterAffine_one_eq_rightEndpoint
  shiftedQuarterAffine_center_eq_shiftedQuarterCenter
  shiftedSemanticLeftEndpoint
  shiftedSemanticRightEndpoint
  shiftedSemanticSeam
  shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
  shiftedSemanticRightEndpoint_q2_of_core_eq_zero
  shiftedSemanticSeam_q2
  shiftedSemanticSeam_q2_of_core_eq_zero
  shiftedSemanticRawMidpoint
  shiftedSemanticRawAffine
  shiftedSemanticRawAffine_zero
  shiftedSemanticRawAffine_one
  shiftedSemanticRawAffine_center_eq_rawMidpoint
  shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
  shiftedSemanticRawMidpoint_q2_of_core_eq_zero
  shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
  shiftedSemanticCorrectedMidpoint
  phaseNormalization_center_ne_zero
  shiftedSemanticCorrection_mul_rawScale
  shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
  shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
  shiftedSemanticRawAffine_q2_of_core_eq_zero
  shiftedSemanticNormalizedEdge
  shiftedSemanticNormalizedEdge_zero
  shiftedSemanticNormalizedEdge_one
  shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
  shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
  normalizedCycleStep
  dyadicCycleStep
  normalizedCycleStep_mul_returnCount
  dyadicCycleStep_mul_returnCount
  semanticPhaseEdge_center
  semanticPhaseEdge_q2_center_of_core_eq_zero
  normalizedPhaseEdge_q2_center_of_core_eq_zero
```

## Boundary and Normalization Targets

The scalar shifted-frame API is now implemented, including endpoint
separation, center half-quarter formulas, and the affine interpolation helper
`shiftedQuarterAffine`.

The first semantic endpoint candidates are also implemented:

```text
left candidate:
  normalized center state of the current quarter edge

right candidate:
  normalized center state of the next quarter edge

seam:
  the old endpoint state between those two edges
```

The candidates all lie on the same `q2` boundary under the core-zero
hypothesis. However, their raw affine midpoint is not the seam state in
general. Lean records the obstruction in two forms:

```text
shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
```

The raw midpoint is a scalar multiple of the seam state, and its square mass
is exactly `1 / 2 * q2 z`. Lean now also records the center correction:

```text
shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
```

Thus the center point itself can be corrected back to the seam and to the
original `q2` boundary.

Lean also verifies the stronger pointwise statement:

```text
shiftedSemanticRawAffine_q2_of_core_eq_zero
```

The raw shifted semantic affine has exactly the same `phaseDepth` profile as
the original affine edge. Therefore the same pointwise normalization is valid:

```text
shiftedSemanticNormalizedEdge
shiftedSemanticNormalizedEdge_leftEndpoint
shiftedSemanticNormalizedEdge_rightEndpoint
shiftedSemanticNormalizedEdge_right_eq_next_left
shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
shiftedSemanticNormalizedPath
shiftedSemanticNormalizedPath_q2_of_core_eq_zero
shiftedSemanticNormalizedLevelPath
shiftedSemanticNormalizedLevelEdge_center_eq_seam
```

The shifted normalized edge starts at the left normalized center candidate,
ends at the right normalized center candidate, stays on the original `q2`
boundary, and reaches the old seam at `phaseCenter`. It is also packaged as a
Mathlib `Path` and as a path internal to the fixed `q2` level set. Adjacent
shifted normalized edges share endpoint states:

```text
shiftedSemanticNormalizedEdge r z 1
  =
shiftedSemanticNormalizedEdge r (semanticAct r z) 0
```

This is the seam-compatibility fact needed before four-edge shifted
concatenation or a cyclic quotient parameter is introduced.

Candidate theorem directions:

```text
semanticPhaseEdge midpoint formula
  semanticPhaseEdge r z (1/2) is the affine average of z and semanticAct r z

q2 midpoint formula
  under core-zero, q2 at the midpoint is (1/2) * q2 z

normalized midpoint boundary formula
  under core-zero, the normalized midpoint returns to the original q2 boundary

shifted-frame conservation
  the normalized edge observed between neighboring centers preserves the same
  boundary law after re-centering
```

The shifted path definition has now been chosen in the same style as
`normalizedPhasePath`: first a `Vec Real` path, then a fixed-`q2` level-set
path. Four-edge shifted concatenation remains a later packaging layer.

## Guardrails

Do not name the first implementation theorem with angle vocabulary.

Preferred names:

```text
halfQuarter
oneEighthPhase
centerShift
endpointAsShiftedCenter
```

Avoid in theorem names for now:

```text
angle
arc
degree
piOverFour
fortyFive
```

Documentation may mention that the future Euclidean bridge will read the
one-eighth phase displacement as `theta = pi / 4`. The Lean core should not
depend on that reading.

## Implementation Plan

1. Implemented: add scalar aliases for `phaseCenter` and `phaseHalfQuarterStep`.
2. Implemented: prove `phaseDepth_center_eq` and `phaseDepth_center_unique`.
3. Implemented: prove `phaseDepth_centered_reflect`.
4. Implemented: add a phase-shift module for global quarter endpoints and centers.
5. Implemented: prove the endpoint-between-centers identity.
6. Implemented: add scalar cycle-step facts for dyadic and positive `k` divisions.
7. Implemented: add scalar shifted-frame endpoints, center, and affine midpoint theorem.
8. Implemented: lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
9. Implemented: name semantic endpoint candidates and prove their raw midpoint obstruction.
10. Implemented: define the corrected shifted midpoint and prove it returns to the seam.
11. Implemented: prove the raw shifted affine has the `phaseDepth` profile.
12. Implemented: define the pointwise normalized shifted semantic edge.
13. Implemented: package the shifted normalized edge as a topological path.
14. Implemented: package the shifted normalized edge inside the fixed `q2` level set.
15. Later: add a Euclidean bridge that reads `1/8` full-cycle
   displacement as the angle `Real.pi / 4`.

## Implemented Tags

```text
[IMPLEMENTED: semantic-cf2d/phase-center-alias]
Add `phaseCenter`, `phaseHalfQuarterStep`, and centered-coordinate wrappers.

[IMPLEMENTED: semantic-cf2d/centered-reflection]
Expose reflection about `phaseCenter` directly, not only as `t -> 1 - t`.

[IMPLEMENTED: semantic-cf2d/endpoint-as-shifted-center]
Prove that the seam endpoint between adjacent quarter edges is the midpoint
between their centers.

[IMPLEMENTED: semantic-cf2d/dyadic-cycle-step]
Expose the dyadic return law `2^n * (1 / 2^n) = 1` as a normalized cycle
parameter fact, not as an angle subdivision.

[IMPLEMENTED: semantic-cf2d/k-division-cycle-step]
Expose the positive `k` return law `k * (1 / k) = 1` for the normalized cycle
parameter before assigning any Euclidean shape.

[IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
Define the shifted semantic normalized edge from neighboring normalized center
states, prove its raw `phaseDepth` profile, prove boundary preservation, and
prove its center is the old seam.

[IMPLEMENTED: semantic-cf2d/shifted-semantic-path]
Package the shifted semantic normalized edge as a `Vec Real` path and as a
fixed-`q2` level-set path. Endpoint aliases, adjacent seam compatibility, and
center-to-action compatibility are exposed for downstream cyclic
concatenation.
```

## Remaining TODO Tags

```text
[TODO: semantic-cf2d/shifted-cyclic-parameter]
Package four shifted normalized paths by an explicit cyclic index when the
next layer needs concatenation or a quotient phase parameter.

[TODO: semantic-cf2d/one-eighth-euclidean-reading]
After the algebraic shifted-frame theorem is closed at the semantic path
level, bridge the one-eighth phase displacement to the Euclidean `pi / 4`
reading.
```
