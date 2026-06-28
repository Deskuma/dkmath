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
shiftedSemanticIndexedBase
shiftedSemanticIndexedEdge
shiftedSemanticIndexedPath
shiftedSemanticIndexedEdge_right_eq_next_left
shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
shiftedSemanticIndexedBase_add_four_of_core_eq_zero
shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
shiftedSemanticIndexedLevelPath
shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
shiftedSemanticIndexedLevelEndpoint_0_1
shiftedSemanticIndexedLevelEndpoint_1_2
shiftedSemanticIndexedLevelEndpoint_2_3
shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
shiftedSemanticFourLevelPath
finFourSucc
finFourSucc_zero
finFourSucc_one
finFourSucc_two
finFourSucc_three
finFourSucc_four_cycle
shiftedSemanticFinBase
shiftedSemanticFinBaseLevelPoint
shiftedSemanticFinEdge
shiftedSemanticFinEdge_leftEndpoint
shiftedSemanticFinEdge_rightEndpoint
shiftedSemanticFinEdge_q2_of_core_eq_zero
shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
shiftedSemanticFinPath
shiftedSemanticFinLevelEdge
shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
shiftedSemanticFinLevelPath
shiftedSemanticFinRightLevelEndpoint_eq_succ_left
shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
shiftedSemanticFinFourLevelPath
shiftedSemanticFourLevelPath_source
shiftedSemanticFourLevelPath_target
shiftedSemanticFinFourLevelPath_source
shiftedSemanticFinFourLevelPath_target
shiftedSemanticFinFourLevelPath_q2
ShiftedFiniteChart
shiftedSemanticFinChartEval
shiftedSemanticFinChartEval_val
shiftedSemanticFinChartEval_at_left
shiftedSemanticFinChartEval_at_right
shiftedFiniteSeamRel
shiftedSemanticFinChartEval_right_eq_succ_left
shiftedSemanticFinChartEval_eq_of_seamRel
shiftedFiniteChartRel
shiftedFiniteChartSetoid
ShiftedCyclicChart
shiftedCyclicChartMk
shiftedCyclicChartMk_eq_mk
shiftedCyclicChartLeft
shiftedCyclicChartRight
shiftedCyclicChartRight_eq_succ_left
shiftedCyclicChartRight_zero_eq_one_left
shiftedCyclicChartRight_one_eq_two_left
shiftedCyclicChartRight_two_eq_three_left
shiftedCyclicChartRight_three_eq_zero_left
continuous_shiftedCyclicChartMk
shiftedSemanticFinChartEval_eq_of_chartRel
continuous_shiftedSemanticFinChartEval_of_fixed_index
continuous_shiftedSemanticFinChartEval
shiftedSemanticCyclicChartEval
shiftedSemanticCyclicChartEval_mk
shiftedSemanticCyclicChartEval_left
shiftedSemanticCyclicChartEval_right
shiftedSemanticCyclicChartEval_right_eq_succ_left
continuous_shiftedSemanticCyclicChartEval
shiftedCyclicChartEdgePath
shiftedCyclicChartEdgePath_apply
shiftedCyclicChartEdgePath_source
shiftedCyclicChartEdgePath_target
shiftedCyclicFourPath
shiftedCyclicFourPath_source
shiftedCyclicFourPath_target
shiftedSemanticCyclicChartEval_edgePath
shiftedSemanticCyclicChartEval_q2
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

The cyclic-index preparation is now also formalized. The `k`th shifted edge
uses the semantic action iterate as its base state:

```text
shiftedSemanticIndexedBase r z k = semanticActIter r k z
```

The indexed edge is the shifted normalized edge at that base. Lean proves:

```text
right endpoint of edge k = left endpoint of edge k+1
center of edge k = indexed base k+1
indexed base (k+4) = indexed base k       under core-zero
indexed edge (k+4) = indexed edge k       under core-zero
```

The same indexed API is available inside the fixed `q2 z` level set, so the
next layer can concatenate edgewise-compatible paths without re-proving
boundary membership.

The four-edge shifted path object is now also available:

```text
shiftedSemanticFourLevelPath
```

It concatenates the first four indexed shifted normalized level paths inside
the fixed `q2` boundary. The first three seams are adjacent endpoint
compatibility facts, and the final seam from edge `3` back to edge `0` uses
the core-zero four-step return law.

The finite cyclic wrapper is now available through `Fin 4`. It keeps the
Nat-indexed API as the source of truth while giving downstream code a bounded
four-state index:

```text
shiftedSemanticFinBase r z i = shiftedSemanticIndexedBase r z i.val
shiftedSemanticFinEdge r z i t = shiftedSemanticIndexedEdge r z i.val t
```

The finite successor `finFourSucc` is defined by `(i.val + 1) % 4`, and Lean
proves the finite seam law:

```text
right endpoint of finite edge i = left endpoint of finite edge (finFourSucc i)
```

This is still a finite cyclic index, not a continuous quotient phase
parameter. The successor has named values for `0 -> 1 -> 2 -> 3 -> 0` and a
four-cycle theorem. Finite shifted edges also expose endpoint aliases and a
center-to-successor-base theorem. The closed shifted four-level path exposes
named source, target, and fixed-`q2` boundary-observation aliases for
downstream observation code. Finite base states are also packaged directly as
fixed-level points.

The pre-quotient chart layer is now explicit:

```text
ShiftedFiniteChart = Fin 4 x unitInterval
```

Chart evaluation maps each chart into the fixed `q2 z` level set. The seam
relation identifies `(i, 1)` with `(finFourSucc i, 0)`, and Lean proves that
chart evaluation is compatible with that relation.

The seam relation is now closed under Mathlib's generated equivalence
relation:

```text
shiftedFiniteChartRel p q =
  Relation.EqvGen shiftedFiniteSeamRel p q
```

The generated relation is packaged as a setoid quotient:

```text
ShiftedCyclicChart = Quot shiftedFiniteChartSetoid
```

Chart evaluation descends to this quotient:

```text
shiftedSemanticCyclicChartEval :
  ShiftedCyclicChart -> LevelSet Real (Vec.q2 z)
```

The computation theorem `shiftedSemanticCyclicChartEval_mk` states that the
quotient evaluation agrees with finite chart evaluation on representatives,
and `shiftedSemanticCyclicChartEval_q2` records that the descended value still
lies on the original fixed boundary. This is only an algebraic seam quotient;
no quotient topology or quotient path structure has been selected yet.

The quotient representative API is now explicit. `shiftedCyclicChartMk` names
the representative constructor, while `shiftedCyclicChartLeft` and
`shiftedCyclicChartRight` name the endpoint representatives. Lean proves the
quotient seam equality:

```text
shiftedCyclicChartRight i =
  shiftedCyclicChartLeft (finFourSucc i)
```

and also exposes the four concrete seam aliases `0 -> 1`, `1 -> 2`,
`2 -> 3`, and `3 -> 0`. Evaluation at quotient endpoint representatives
computes back to the finite left and right level endpoints, and quotient
evaluation is seam-compatible by rewriting through the quotient equality.

The first topological quotient layer is also implemented.

```text
Algebraic quotient:
  identifies seam endpoints as equal chart points.

Topological quotient:
  additionally gives the glued chart space the quotient topology.

Boundary evaluation:
  is continuous after representative-level evaluation and the quotient-lift
  theorem are connected.
```

Lean now proves continuity of `shiftedCyclicChartMk`, continuity of finite
chart evaluation before quotienting, and continuity of the descended
fixed-`q2` boundary evaluation. This is still not a Euclidean angle parameter.
The quotient traversal path layer is now also available. For each finite
index, `shiftedCyclicChartEdgePath i` traverses the representative charts
`(i, t)` inside the quotient. The four finite quotient edges concatenate,
using only the quotient seam equalities, into the closed path
`shiftedCyclicFourPath`.

The local evaluation comparison is proved:

```text
shiftedSemanticCyclicChartEval hcore z
  (shiftedCyclicChartEdgePath i t)
=
shiftedSemanticFinLevelEdge hcore z i t
```

The full comparison between evaluation of `shiftedCyclicFourPath` and the
existing fixed-`q2` four-level path is intentionally left as a TODO because it
requires path-trans cast normalization lemmas. This is still not a Euclidean
angle parameter.

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
path. The first four shifted level paths are now also concatenated into a
closed fixed-boundary path object.

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
15. Implemented: index shifted normalized edges by semantic action iterates.
16. Implemented: prove indexed adjacent seam compatibility and center-to-next-base compatibility.
17. Implemented: prove core-zero four-step return for indexed bases, endpoints, and edge functions.
18. Implemented: package indexed shifted paths inside the fixed `q2` level set.
19. Implemented: prove the four endpoint compatibility facts for indexed shifted level paths.
20. Implemented: concatenate the four indexed shifted level paths into a closed fixed-`q2` path.
21. Implemented: add `Fin 4` wrappers for shifted bases, edges, paths, level edges, and level paths.
22. Implemented: prove the finite successor seam law on `Fin 4`.
23. Implemented: add small-step and four-cycle API for `finFourSucc`.
24. Implemented: add finite endpoint aliases and center-to-successor-base compatibility.
25. Implemented: add source and target aliases for the closed shifted four-level path.
26. Implemented: add finite base level-point wrappers.
27. Implemented: add finite closed-path fixed-`q2` observation.
28. Implemented: add finite chart evaluation into the fixed `q2` level set.
29. Implemented: add finite seam relation and chart-evaluation seam compatibility.
30. Implemented: close the finite seam relation under `Relation.EqvGen`.
31. Implemented: package the generated relation as `ShiftedCyclicChart`.
32. Implemented: descend chart evaluation to the quotient and expose its
    representative computation theorem.
33. Implemented: add quotient representative constructor aliases.
34. Implemented: add quotient left/right endpoint representatives.
35. Implemented: prove quotient seam equality and four finite seam aliases.
36. Implemented: expose quotient evaluation at endpoint representatives and
    quotient evaluation seam compatibility.
37. Implemented: connect Mathlib's quotient topology to `ShiftedCyclicChart`.
38. Implemented: prove representative-level chart evaluation continuity.
39. Implemented: prove descended quotient evaluation continuity.
40. Implemented: package one quotient chart edge path.
41. Implemented: concatenate the first four quotient edge paths into a closed
    quotient path.
42. Implemented: prove the local edge evaluation comparison against the
    fixed-`q2` finite level edge.
43. Later: compare the evaluated closed quotient path with the existing
    fixed-`q2` four-level path after path-trans cast normalization lemmas.
44. Later: add a Euclidean bridge that reads `1/8` full-cycle
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

[IMPLEMENTED: semantic-cf2d/shifted-indexed-edge]
Index shifted normalized edges by semantic action iterates. Prove adjacent
indexed seam compatibility, center-to-next-base compatibility, four-step
return for bases and edge functions, and fixed-`q2` indexed level-set path
wrappers.

[IMPLEMENTED: semantic-cf2d/shifted-four-level-path]
Prove the four seam compatibility facts and concatenate the first four indexed
shifted normalized level paths into one closed fixed-`q2` path object.

[IMPLEMENTED: semantic-cf2d/shifted-fin-four]
Expose the shifted cyclic index through `Fin 4` wrappers for bases, edges,
paths, fixed-`q2` level edges, and fixed-`q2` level paths. Add a finite
successor and prove the corresponding cyclic seam law. The successor has
named small-step facts and a four-cycle law, finite edges expose endpoint and
center-to-successor-base compatibility, and the closed shifted path has named
source and target aliases.

[IMPLEMENTED: semantic-cf2d/shifted-fin-observation]
Package finite base states as fixed-`q2` level points. Expose the finite
center-to-successor-base theorem at the level-point API and add source,
target, and fixed-`q2` observation aliases for the finite closed shifted path.

[IMPLEMENTED: semantic-cf2d/shifted-finite-chart]
Expose `ShiftedFiniteChart = Fin 4 x unitInterval`, evaluate it into the
fixed `q2` boundary, record the finite seam relation, and prove chart
evaluation compatibility across seams.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-chart]
Close the finite seam relation under `Relation.EqvGen`, package it as the
setoid quotient `ShiftedCyclicChart`, and descend chart evaluation to a
fixed-`q2` boundary-valued quotient evaluation. The computation theorem on
representatives and the descended `q2` observation are also exposed.
Representative constructor aliases, endpoint representatives, quotient seam
equality, concrete seam aliases, endpoint evaluation theorems, and quotient
evaluation seam compatibility are also exposed.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-topology]
Connect Mathlib's quotient topology on `Quot` to `ShiftedCyclicChart`. The
representative map, finite chart evaluation before quotienting, and descended
fixed-`q2` quotient evaluation are continuous. This is a quotient-topology
statement only; it does not select a quotient path structure.

[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path]
Package one quotient chart edge path, concatenate the first four quotient edge
paths into a closed quotient path by quotient seam equalities, expose source
and target aliases, and prove the local edge evaluation comparison with the
fixed-`q2` finite level edge.
```

## Remaining TODO Tags

```text
[TODO: semantic-cf2d/shifted-cyclic-path-eval]
Compare evaluation of the closed quotient path with the fixed-`q2` four-level
path after path-trans cast normalization lemmas are available.

[TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
Develop any additional quotient-space structure only after the descended
continuous evaluation API has downstream consumers.

[TODO: semantic-cf2d/one-eighth-euclidean-reading]
After the algebraic shifted-frame theorem is closed at the semantic path
level, bridge the one-eighth phase displacement to the Euclidean `pi / 4`
reading.
```
