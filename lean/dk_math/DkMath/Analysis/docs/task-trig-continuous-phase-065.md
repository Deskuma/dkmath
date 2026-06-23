# Task 065: Continuous Four-Phase Transition Design

## Status

Implementation in progress after the discrete exact-order-four result.

The scalar profile, affine master edge, endpoint laws, exact core-zero `q2`
profile, and half-fold observation theorem are implemented in
`DkMath.Analysis.DkReal.SemanticCF2DPhase`.

The coordinate-product topology, continuous edge paths, four-edge
concatenation, and core-zero closed path are implemented in
`DkMath.CosmicFormula.Rotation.CF2D.Topology` and
`DkMath.Analysis.DkReal.SemanticCF2DPath`.

The positive reciprocal-square-root correction, normalized master edge,
endpoint laws, continuity, and fixed-`q2` theorem are implemented in
`DkMath.Analysis.DkReal.SemanticCF2DNormalize`.

That module also implements all four normalized action translates, their
seams, common fixed-`q2` law, phase-index periodicity, continuous paths, and
the resulting closed four-phase path.

The same construction is now packaged directly in
`LevelSet Real (Vec.q2 z)`. The level-set subtype carries its inherited
topology, and the final closed path cannot leave the boundary by construction.

`CF2D.EuclideanPhase` interprets this level set as the explicit coordinate
equation `x^2 + y^2 = rho2` by a homeomorphism. The already-constructed closed
path is mapped through that bridge; it is not reconstructed geometrically.

The coordinate equation is further identified with Mathlib's standard L2
metric sphere in `EuclideanSpace Real (Fin 2)`, of radius `sqrt rho2`.
This avoids confusing the ordinary product norm on `Real × Real` with the
Euclidean L2 norm.

The core-zero semantic action is then identified with the standard coordinate
quarter-turn linear isometry `(x,y) ↦ (-y,x)`. This introduces the geometric
name only after the linear isometry model is available.

The current implementation proves a four-state return:

```text
z
  -> A z
  -> A^2 z
  -> A^3 z
  -> z
```

for the semantic core-zero action `A`. The next task is to fill each discrete
transition continuously without assuming a circle or angle in advance.

## Design Principle

The construction should proceed in this order:

```text
discrete four-state action
  -> one affine transition template
  -> four translated copies of that template
  -> seam-compatible closed path
  -> symmetric boundary-defect profile
  -> optional normalization back to the q2 boundary
  -> Euclidean circle and angle interpretation
```

This preserves the existing rule: geometry is an interpretation of the
algebraic transition mechanism, not an input to it.

## Important Distinction

Affine interpolation between consecutive states is continuous, but it does not
preserve `q2` between the endpoints.

Four affine edges joined at their endpoints form a closed piecewise-linear
loop. They do not yet form a `q2` level set. Therefore the following objects
must remain separate:

1. the cyclic parameter space obtained by gluing four intervals;
2. the piecewise-affine target loop;
3. the normalized target path lying on a fixed `q2` boundary;
4. the later Euclidean interpretation of that normalized boundary as a circle.

Calling the affine loop a circle would collapse these layers too early.

## I. One Master Transition

Let `A := semanticAct r`, under the hypothesis that the semantic core of `r`
is zero. For a real parameter `t`, define the master transition:

```text
E z t = (1 - t) • z + t • A z.
```

The intended Lean definition is coordinatewise, or through the real module
structure once `Vec Real` is bundled appropriately:

```lean
def semanticPhaseEdge
    (r : UnitKernel DkNNRealQ) (z : Vec Real) (t : Real) : Vec Real
```

Required endpoint theorems:

```text
E z 0 = z
E z 1 = A z
```

Required continuity theorem:

```text
Continuous (fun t => E z t)
```

This is the vector-valued analogue of `DkMath.Analysis.gapLine`.

## II. One Pattern, Four Translates

Define the `k`th phase edge from the one master edge:

```text
E_k z t = A^[k] (E z t).
```

This is the precise meaning of “one transition pattern, turned four times.”
The other three transitions are not separately defined formulas.

Required theorems:

```text
E_k z 0 = A^[k] z
E_k z 1 = A^[k+1] z
E_k z 1 = E_(k+1) z 0
E_(k+4) z t = E_k z t
```

The seam theorem gives endpoint compatibility. Exact action order four gives
periodicity in the phase index.

## III. Continuous Closed Path

The first implementation should use Mathlib `Path` rather than immediately
constructing a custom quotient circle.

Each edge becomes:

```text
Path (A^[k] z) (A^[k+1] z)
```

The four paths are concatenated with `Path.trans`. The final endpoint equals
the initial point by exact action order four, producing a closed path.

This path is continuous and piecewise affine. It is not globally affine, and
endpoint identification does not turn it into a linear map.

A custom cyclic parameter quotient may be introduced later:

```text
(Fin 4 × unitInterval) / ((k,1) ~ (k+1,0)).
```

That quotient is a parameter-cycle object. Its homeomorphism with a standard
topological circle belongs to a later interpretation theorem.

## IV. Half-Fold Symmetry

For the core-zero action, direct polynomial calculation should give:

```text
q2 (E z t) = ((1 - t)^2 + t^2) * q2 z.
```

Define the scalar transition profile:

```text
phaseDepth t = (1 - t)^2 + t^2.
```

Then:

```text
phaseDepth (1 - t) = phaseDepth t
phaseDepth 0 = 1
phaseDepth 1 = 1
phaseDepth (1/2) = 1/2
```

This is the desired half-fold pattern. The second half of the boundary-defect
profile is determined by reflection of the first half about `t = 1/2`.

The state-valued path itself is not equal under `t ↦ 1-t`; its endpoints are
reversed. The fold symmetry belongs first to the scalar `q2` profile, or to a
paired transition carrying both orientations. This distinction should be
preserved in theorem names.

## V. Relation To DkReal

The construction follows the same architecture as `DkReal`:

```text
finite interval observations
  -> nested refinement
  -> a unique semantic Real value
```

However, the first continuity implementation should remain in the semantic
real target:

```text
t : Real
E z t : Vec Real.
```

Reasons:

1. the target transition uses signed coordinates;
2. the current quotient core is nonnegative;
3. `DkReal` does not yet carry the topology needed to state path continuity;
4. the semantic bridge already isolates noncomputable Real interpretation.

The DkReal contribution should initially be a computable approximation layer
for the parameter:

```text
rational subinterval samples
nested parameter intervals
semantic evaluation of the completed parameter
```

Do not claim that the current DkReal API already provides a topological path
domain. The existing nested-interval method supplies the completion strategy,
not yet the final continuity interface.

## VI. Returning To The Boundary

Because affine interpolation leaves the `q2` boundary, a separate
normalization is required.

For nonzero `z`, the profile satisfies:

```text
phaseDepth t >= 1/2 > 0.
```

This makes a later normalization possible:

```text
N z t =
  (1 / sqrt (phaseDepth t)) • E z t
```

for a unit `q2` boundary, with the corresponding scaled formula for general
`q2 z`.

Expected theorem:

```text
q2 (N z t) = q2 z.
```

This is the first point where square root, division, and their continuity are
genuinely required. It belongs in a separate semantic/analytic file, not in
the affine transition core.

## VII. Proposed Module Boundary

### Algebraic and semantic transition core

```text
DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
```

Responsibilities:

```text
semanticPhaseEdge
four translated edges
endpoint and seam laws
q2 profile formula
fold symmetry
```

### Topological path bridge

```text
DkMath/Analysis/DkReal/SemanticCF2DPath.lean
```

Responsibilities:

```text
Continuous edge maps
Mathlib Path values
four-edge concatenation
closed-path endpoint theorem
```

### Boundary normalization

```text
DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
```

Responsibilities:

```text
strict positivity of phaseDepth
sqrt/division normalization
q2 preservation of the normalized path
continuity of normalization
```

### Euclidean and angular interpretation

```text
DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
```

Responsibilities:

```text
identify q2 with Euclidean squared norm
interpret normalized closed paths on circles
introduce angle only after the circle model is available
compare with Real.sin and Real.cos
```

## VIII. First Implementation Milestone

The next safe implementation target is deliberately smaller than the full
continuous circle:

1. define `semanticPhaseEdge`;
2. prove its endpoint and continuity laws;
3. define `semanticPhaseEdgeAt k` from action iteration;
4. prove seam compatibility and four-phase repetition;
5. prove the `q2` profile formula;
6. prove `phaseDepth (1-t) = phaseDepth t`;
7. package the first edge as a Mathlib `Path`.

Stop before normalization. At that checkpoint Lean will have verified the
continuous four-edge transition mechanism and its half-fold symmetry, while
the distinction between polygonal filling and boundary-valued motion remains
explicit.

## IX. Tagged Future Work

```text
[IMPLEMENTED: semantic-cf2d-phase/master-edge]
[IMPLEMENTED: semantic-cf2d-phase/four-translates]
[IMPLEMENTED: semantic-cf2d-phase/half-fold-profile]
[IMPLEMENTED: semantic-cf2d-phase/path-topology]
[IMPLEMENTED: semantic-cf2d-phase/path-concatenation]
[IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
[IMPLEMENTED: semantic-cf2d-phase/normalized-four-path]
[IMPLEMENTED: semantic-cf2d-phase/levelset-path]
[IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
[IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
[IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry]
[IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two]
[IMPLEMENTED: semantic-cf2d-phase/dyadic-refinement]
`SemanticCF2DDyadic` defines the finite nodes `k / 2^n`, proves their endpoint,
unit-interval, reflection, even-child, odd-child midpoint, and reflected
phase-depth laws.
[IMPLEMENTED: semantic-cf2d-phase/finite-depth-refinement]
`SemanticCF2DRefinement` proves reflection and even-child inheritance for
dyadic depth and normalization. Quadraticity gives the exact odd-child law:
its depth is the average adjacent-parent depth minus
`1 / (2 * (2^n)^2)`.
[TODO: semantic-cf2d-phase/correction-composition] Select and prove an
aggregate composition law for local boundary corrections. Do not assume that
it is an infinite product or a logarithmic sum before its finite form is
established.
[TODO: semantic-cf2d-phase/gaussian-limit]
[TODO: semantic-cf2d-phase/pi-identification]
```

The longer route from this local quadratic profile to a possible
pre-geometric normalization constant is recorded in
`research-pregeometric-pi-program-067.md`. That document separates proved
transition laws from conjectural refinement, Gaussian, and identification
stages.
