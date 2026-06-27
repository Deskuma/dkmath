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

## Proposed Lean Surface

The scalar names can live near `SemanticCF2DPhase.lean`:

```lean
def phaseCenter : ℝ := 1 / 2
def phaseHalfQuarterStep : ℝ := 1 / 8

def centeredPhaseCoord (t : ℝ) : ℝ :=
  t - phaseCenter
```

The four-edge/global parameter names can live in a small new module, for
example `SemanticCF2DPhaseShift.lean`:

```lean
def globalQuarterEndpoint (k : ℕ) : ℝ :=
  (k : ℝ) / 4

def globalQuarterCenter (k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 2) / 4
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
```

The last theorem is the main checkpoint. It says that, after shifting the
observation frame from endpoints to neighboring centers, the old endpoint is
now the midpoint.

## Boundary and Normalization Targets

After the scalar shift theorem, the next target is to lift it back to the
semantic edge and normalized edge APIs.

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

The last item should be delayed until the exact shifted path definition is
chosen. The scalar theorem should come first.

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

1. Add scalar aliases for `phaseCenter` and `phaseHalfQuarterStep`.
2. Prove `phaseDepth_center_eq` and `phaseDepth_center_unique` as API aliases.
3. Prove `phaseDepth_centered_reflect`.
4. Add a small phase-shift module for global quarter endpoints and centers.
5. Prove the endpoint-between-centers identity.
6. Lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
7. Only after that, add a Euclidean bridge that reads `1/8` full-cycle
   displacement as the angle `Real.pi / 4`.

## TODO Tags

```text
[TODO: semantic-cf2d/phase-center-alias]
Add `phaseCenter`, `phaseHalfQuarterStep`, and centered-coordinate wrappers.

[TODO: semantic-cf2d/centered-reflection]
Expose reflection about `phaseCenter` directly, not only as `t -> 1 - t`.

[TODO: semantic-cf2d/endpoint-as-shifted-center]
Prove that the seam endpoint between adjacent quarter edges is the midpoint
between their centers.

[TODO: semantic-cf2d/one-eighth-euclidean-reading]
After the algebraic shift theorem is closed, bridge the one-eighth phase
displacement to the Euclidean `pi / 4` reading.
```
