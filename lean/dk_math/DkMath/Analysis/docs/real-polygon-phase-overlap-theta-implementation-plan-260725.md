# Real Polygon Phase Overlap and Continuous Theta Implementation Plan

## Status

Design note only. No Lean implementation is claimed by this document.

The observation-oriented companion note is:

[実数正多角位相・重なり偏角・連続化観測](../../../../../docs/not_implements/real-polygon-phase-overlap-angle-continuation-260725.md)

This plan records a parameter-side route from finite CF2D regular orbits to a real phase scale, a local overlap coordinate, a continuous `q2`-preserving orbit, and a later Euclidean `theta` reading.

## 1. Objective

The current DkMath route already has the following layers.

| Layer | Current implementation |
|---|---|
| Exact four-state semantic action | `DkMath.Analysis.DkReal.SemanticCF2D` |
| Affine phase filling and half-fold `q2` profile | `DkMath.Analysis.DkReal.SemanticCF2DPhase` |
| Normalized fixed-`q2` phase path | `DkMath.Analysis.DkReal.SemanticCF2DNormalize` |
| Scalar phase-center shifts | `DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` |
| Abstract and normalized finite cycle division | `DkMath.CosmicFormula.Rotation.CF2D.CycleDivision` |
| Exact finite regular orbit | `DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit` |
| Euclidean equal-step reading | `DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit` |
| Gauss-Wantzel arithmetic form | `DkMath.NumberTheory.EuclideanGeometry.FermatForm` |
| Algebraic quadratic-expression model | `DkMath.NumberTheory.EuclideanGeometry.QuadraticConstructible` |

The missing parameter architecture is a common object that can express all of the following without first defining polygon edges.

1. A positive real cycle scale $n$.
2. A basic phase cell of width $1/n$.
3. The completed-cell count $\lfloor n\rfloor$.
4. The local overlap $n-\lfloor n\rfloor$ in $[0,1)$.
5. The global overlap argument $(n-\lfloor n\rfloor)/n$.
6. Exact closure of completed cells and the overlap cell.
7. Natural-number regular orbits as integer samples.
8. A continuous semantic orbit on a fixed `q2` level.
9. A Euclidean `theta` reading attached only at the final bridge.

## 2. Central scalar laws

Let $n>0$.

$$
m=\lfloor n\rfloor
$$

$$
\alpha=n-\lfloor n\rfloor
$$

$$
0\leq\alpha<1
$$

The normalized full-cycle cell width is:

$$
h_n=\frac{1}{n}
$$

The local cell chart is:

$$
\frac{[0,1)}{n}=\left[0,\frac{1}{n}\right)
$$

The overlap argument is:

$$
\omega_n=\frac{\alpha}{n}
$$

The closure law is:

$$
\frac{m}{n}+\frac{\alpha}{n}=1
$$

The unoriented-direction version is:

$$
\frac{m}{2n}+\frac{\alpha}{2n}=\frac{1}{2}
$$

These identities are the first implementation milestone. They require no CF2D kernel, circle, angle, or trigonometric function.

## 3. Proposed module boundary

### 3.1 Scalar real-phase chart

Proposed file:

```text
DkMath/Analysis/DkReal/RealPhaseOverlap.lean
```

This file should contain only real scalar arithmetic, floor/fractional-part facts, interval membership, closure laws, and carry-chart data.

Candidate definitions:

```lean
def completedPhaseCells (n : ℝ) : ℕ := ⌊n⌋₊

def localPhaseOverlap (n : ℝ) : ℝ :=
  n - (completedPhaseCells n : ℝ)

def phaseCellWidth (n : ℝ) : ℝ :=
  1 / n

def completedPhaseWidth (n : ℝ) : ℝ :=
  (completedPhaseCells n : ℝ) / n

def overlapPhaseWidth (n : ℝ) : ℝ :=
  localPhaseOverlap n / n
```

The exact floor API may be adjusted after checking the current Mathlib version. The semantic content must remain the same.

Primary theorem candidates:

```lean
theorem completedCells_add_localOverlap
    {n : ℝ} (hn : 0 ≤ n) :
    (completedPhaseCells n : ℝ) + localPhaseOverlap n = n

theorem localPhaseOverlap_nonneg
    {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ localPhaseOverlap n

theorem localPhaseOverlap_lt_one
    {n : ℝ} (hn : 0 ≤ n) :
    localPhaseOverlap n < 1

theorem completedWidth_add_overlapWidth
    {n : ℝ} (hn : 0 < n) :
    completedPhaseWidth n + overlapPhaseWidth n = 1

theorem overlapPhaseWidth_mem_cell
    {n : ℝ} (hn : 0 < n) :
    overlapPhaseWidth n ∈ Set.Ico 0 (phaseCellWidth n)

theorem completedDirectionWidth_add_overlapDirectionWidth
    {n : ℝ} (hn : 0 < n) :
    completedPhaseWidth n / 2 + overlapPhaseWidth n / 2 = 1 / 2
```

### 3.2 Carry seam

A raw fractional-part coordinate has a jump at each integer. Continuity must therefore be stated on a chart system or quotient carrying the identification:

$$
(m,1)\sim(m+1,0)
$$

The first implementation may avoid a custom quotient and prove local chart laws on `Set.Ico 0 1`.

A later file may introduce:

```text
DkMath/Analysis/DkReal/RealPhaseCarry.lean
```

Possible representations include a quotient of closed cells, an `AddCircle`-based phase, or an atlas whose transition map performs the carry.

The implementation must not claim continuity of the standalone fractional-part function at integers.

### 3.3 CF2D real phase orbit

Proposed file:

```text
DkMath/CosmicFormula/Rotation/CF2D/RealPhaseOrbit.lean
```

This file should import the scalar phase chart and `CycleDivision.lean`.

It must not be placed below a module that would create an import cycle with `CycleDivision.lean`, because `CycleDivision.lean` already imports the semantic phase-shift layer.

The first semantic realization may use the existing `normalizedRealKernelFamily`.

Candidate definitions:

```lean
def scaledPhase (n t : ℝ) : ℝ :=
  t / n

def realPhaseKernel (n t : ℝ) : UnitKernel ℝ :=
  normalizedRealKernelFamily.kernel (scaledPhase n t)

def realPhaseOrbit (n : ℝ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  UnitKernel.act (realPhaseKernel n t) z
```

Primary theorem candidates:

```lean
theorem scaledPhase_add_period
    {n : ℝ} (hn : n ≠ 0) (t : ℝ) :
    scaledPhase n (t + n) = scaledPhase n t + 1

theorem realPhaseKernel_add_period
    {n : ℝ} (hn : n ≠ 0) (t : ℝ) :
    realPhaseKernel n (t + n) = realPhaseKernel n t

theorem realPhaseOrbit_add_period
    {n : ℝ} (hn : n ≠ 0) (z : Vec ℝ) (t : ℝ) :
    realPhaseOrbit n z (t + n) = realPhaseOrbit n z t

theorem realPhaseOrbit_q2
    (n : ℝ) (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (realPhaseOrbit n z t) = Vec.q2 z
```

The half-cycle theorem should distinguish oriented states from unoriented directions.

```lean
theorem realPhaseOrbit_add_halfPeriod
    {n : ℝ} (hn : n ≠ 0) (z : Vec ℝ) (t : ℝ) :
    realPhaseOrbit n z (t + n / 2) = -realPhaseOrbit n z t
```

The corresponding direction-level theorem should identify the two states only after quotienting by sign.

## 4. Closing Overlap kernel law

Let $m=\lfloor n\rfloor$ and $\alpha=n-m$.

Define the completed-step kernel and overlap kernel by phases $m/n$ and $\alpha/n$.

The central kernel theorem should be:

$$
K\left(\frac{m}{n}\right)\star K\left(\frac{\alpha}{n}\right)=K(1)=1
$$

Candidate theorem shape:

```lean
theorem completedKernel_mul_overlapKernel_eq_one
    {n : ℝ} (hn : 0 < n) :
    realPhaseKernel n (completedPhaseCells n : ℝ) *
      realPhaseKernel n (localPhaseOverlap n) = 1
```

This theorem is the kernel-level form of:

$$
\frac{m}{n}+\frac{\alpha}{n}=1
$$

The overlap kernel must not be described as a numerical error term. It is the exact closing factor for the chosen moving phase chart.

## 5. Moving coordinate frame

Proposed definitions in `RealPhaseOrbit.lean`:

```lean
def movingPhaseFrame (n t : ℝ) (w : Vec ℝ) : Vec ℝ :=
  UnitKernel.act (realPhaseKernel n (-t)) w
```

Expected cancellation theorem:

```lean
theorem movingFrame_realPhaseOrbit
    {n : ℝ} (hn : n ≠ 0) (z : Vec ℝ) (t : ℝ) :
    movingPhaseFrame n t (realPhaseOrbit n z t) = z
```

This theorem formalizes the observation that the orbit moves in a fixed frame but is stationary in the co-moving frame.

The Euclidean location of the overlap chart is coordinate-dependent. The overlap width is the invariant scalar datum.

## 6. Natural-number compatibility

The real-scale API must recover the existing finite regular orbit exactly.

For positive $k\in\mathbb N$, the one-unit-time real phase kernel should equal the existing `regularKernel k`.

Candidate theorem:

```lean
theorem realPhaseKernel_nat_one_eq_regularKernel
    {k : ℕ} (hk : 0 < k) :
    realPhaseKernel (k : ℝ) 1 = regularKernel k
```

Integer samples should recover `kernelOrbitVertex` and `regularVertex`.

```lean
theorem realPhaseOrbit_natSample_eq_kernelOrbitVertex
    {k j : ℕ} (hk : 0 < k) :
    realPhaseOrbit (k : ℝ) (Vec.one ℝ) (j : ℝ) =
      kernelOrbitVertex (regularKernel k) (Vec.one ℝ) j
```

A `Fin k` wrapper should then identify the sample with `regularVertex k j`.

This bridge is essential. Without it, the real phase scale would be a parallel API rather than a genuine extension of the existing regular-orbit layer.

## 7. Continuous semantic realization

The first backend may use `normalizedRealKernelFamily`, whose coordinates are realized through Mathlib real sine and cosine.

This gives a semantic continuity theorem candidate:

```lean
theorem continuous_realPhaseOrbit
    {n : ℝ} (hn : n ≠ 0) (z : Vec ℝ) :
    Continuous (fun t : ℝ => realPhaseOrbit n z t)
```

This result would provide a global continuous fixed-`q2` orbit immediately.

It must be labeled as a semantic real realization. It does not yet construct an intrinsic DkMath kernel continuum without trigonometric functions.

The distinction is:

| Layer | Meaning |
|---|---|
| Real phase chart | Intrinsic normalized parameter architecture |
| `normalizedRealKernelFamily` | First semantic backend using `Real.cos` and `Real.sin` |
| Future intrinsic kernel continuum | DkMath construction from refinement and completion |
| Euclidean theta | Final interpretation through `Real.pi` |

## 8. Relation to the existing normalized affine path

`SemanticCF2DPhase.lean` and `SemanticCF2DNormalize.lean` construct a path between four exact semantic states by affine filling followed by `q2` normalization.

`RealPhaseOrbit.lean` would instead use a continuously parameterized unit kernel and therefore preserve `q2` directly.

These two paths have the same quarter-state endpoints after the appropriate bridge, but they must not be claimed equal with the same local parameter.

The normalized affine chord generally induces a nonuniform Euclidean angular speed. Equality with the uniform real phase orbit requires a reparameterization theorem.

A later milestone should prove one of the following.

1. Equality after an explicit monotone local reparameterization.
2. Equality of image sets on each quarter boundary.
3. Homotopy or path equivalence preserving endpoints and orientation.

The first implementation should stop at endpoint compatibility and fixed-`q2` image comparison.

## 9. DkMath argument and Euclidean theta

Proposed pre-geometric argument definitions:

```lean
def dkPhaseArgument (n t : ℝ) : ℝ :=
  t / n

def dkOverlapArgument (n : ℝ) : ℝ :=
  overlapPhaseWidth n
```

The scalar argument is normalized in full-cycle units. No `Real.pi` is required.

Proposed Euclidean bridge file:

```text
DkMath/CosmicFormula/Rotation/CF2D/EuclideanRealPhase.lean
```

Candidate Euclidean definition:

```lean
def euclideanTheta (n t : ℝ) : ℝ :=
  normalizedPhaseAngle (dkPhaseArgument n t)
```

Expected theorem:

```lean
theorem euclideanTheta_eq_two_pi_mul
    (n t : ℝ) :
    euclideanTheta n t = (t / n) * (2 * Real.pi)
```

Natural-number compatibility should recover the existing theorem `regularStepAngle_eq_two_pi_div`.

The implementation order must remain:

```text
real phase scale
  -> local cell and overlap coordinate
  -> kernel-family action
  -> q2-preserving continuous orbit
  -> Euclidean theta reading
```

## 10. Gauss-Wantzel extension analysis

The current public entry `DkMath.EuclideanGeometry` explicitly does not claim a complete Gauss-Wantzel theorem.

The present implementation has four relevant pieces.

1. `IsGaussWantzelIndex n` records the arithmetic Fermat-prime form.
2. `regularKernel n` and `regularVertex n` produce an exact finite CF2D orbit for every positive natural $n$.
3. `EuclideanRegularOrbit.lean` reads the successor as rotation by $2\pi/n$.
4. `QuadraticConstructible.lean` proves that a quadratically constructible one-step kernel generates a quadratically constructible orbit.

The principal missing implication remains:

```lean
IsGaussWantzelIndex n ->
  QuadraticallyConstructibleUnitKernel (regularKernel n)
```

The Real Polygon Phase work does not prove this implication.

It can, however, fill a separate missing layer:

```text
finite exact-order orbit
  -> normalized phase sample
  -> real phase chart
  -> continuous q2 orbit
  -> Euclidean theta interpretation
```

It also supplies a clean compatibility target for Gauss-Wantzel samples:

```lean
IsGaussWantzelIndex n ->
  QuadraticallyConstructibleRegularOrbit n ->
  finite samples of realPhaseOrbit (n : ℝ)
```

The following questions should be recorded, but not answered prematurely.

1. Can the Fermat-prime quadratic tower construct the phase kernel at every natural Gauss-Wantzel index?
2. Can the resulting finite constructible samples be embedded into the real phase orbit without importing polygon edges?
3. Does the overlap chart provide a useful completion interface for nonconstructible or noninteger phase scales?
4. Can a DkReal refinement backend realize the same phase continuum without defining it through `Real.sin` and `Real.cos`?

The new phase layer may complete the finite-to-continuous and parameter-to-theta sides of the DkMath program. It does not replace the arithmetic-to-quadratic or quadratic-to-incidence bridges required by the classical theorem.

## 11. Proposed implementation roadmap

### Milestone RPO-001: Scalar phase decomposition

Implement `RealPhaseOverlap.lean`.

Required results:

```text
floor decomposition
local overlap bounds
cell-width positivity
closing overlap identity
overlap interval membership
half-cycle identity
```

### Milestone RPO-002: Carry chart

Record the seam relation:

$$
(m,1)\sim(m+1,0)
$$

Prove that the reconstructed total scale is compatible across the seam.

Do not require a quotient topology in the first patch.

### Milestone RPO-003: Semantic real phase kernel

Implement `RealPhaseOrbit.lean` using `normalizedRealKernelFamily` as the first backend.

Required results:

```text
period n
half-period sign reversal
q2 preservation
closing overlap kernel law
moving-frame cancellation
```

### Milestone RPO-004: Natural finite-orbit compatibility

Prove exact compatibility with:

```text
regularPhaseStep
regularKernel
kernelOrbitVertex
regularVertex
```

### Milestone RPO-005: Continuity and level-set packaging

Package the orbit directly in `LevelSet ℝ (Vec.q2 z)`.

Prove continuity in the semantic real backend.

Avoid reconstructing a Euclidean circle at this stage.

### Milestone RPO-006: Euclidean theta bridge

Implement `EuclideanRealPhase.lean`.

Prove agreement with the existing natural-step angle theorem.

Keep all `Real.pi` references in this interpretation layer.

### Milestone RPO-007: Existing path comparison

Compare the real phase orbit with the normalized affine four-edge path.

Start with endpoint and image-set theorems. Defer uniform-parameter equality until a correct reparameterization is available.

### Milestone RPO-008: Gauss-Wantzel bridge assessment

Add theorem statements or TODO documentation for:

```text
Gauss-Wantzel index to constructible regular kernel
constructible regular kernel to real-phase finite sample
quadratic expression to geometric construction
```

No theorem should be added with an unproved geometric meaning hidden in a definition.

### Milestone RPO-009: DkReal computable approximation

After the semantic real API is stable, design rational or DkReal approximants for:

```text
real cycle scale
local overlap argument
phase kernel samples
moving-frame samples
```

Use common-refinement or least-common-multiple synchronization for comparisons between distinct rational scales.

## 12. Public import plan

After each layer is implemented and stable, update imports in this order.

```text
DkMath.Analysis
  -> RealPhaseOverlap

DkMath.EuclideanGeometry
  -> RealPhaseOrbit
  -> EuclideanRealPhase
```

The scalar Analysis entry should not import the Gauss-Wantzel arithmetic layer.

The EuclideanGeometry aggregate may import the final compatibility bridge after dependency-cycle review.

## 13. Guardrails

1. Do not define real $n$ as the cardinality of a literal vertex type.
2. Do not treat the overlap kernel as an approximation error.
3. Do not confuse overlap location with overlap width.
4. Do not claim continuity of raw fractional part across integer carries.
5. Do not place `Real.pi` in the scalar overlap module.
6. Do not identify the semantic trigonometric backend with an intrinsic DkMath construction.
7. Do not claim the real phase orbit equals the normalized affine path without a reparameterization theorem.
8. Do not claim that this plan completes the Gauss-Wantzel constructibility theorem.
9. Preserve the existing principle that polygon edges and interiors are downstream Euclidean interpretations.
10. Preserve `q2` as the primary boundary detector.

## 14. Completion criterion

The parameter-side task is complete when Lean proves a commuting compatibility diagram of the following form.

```text
positive natural k and finite index j
  -> existing regularVertex k j
  -> realPhaseOrbit (k : ℝ) at integer time j
  -> same q2 state
  -> Euclidean rotation reading by 2*pi*j/k
```

The real extension is complete when the same orbit is defined for every positive real scale $n$, is periodic with period $n$, preserves `q2`, carries the exact Closing Overlap factor, and admits a continuous semantic realization.

The intrinsic DkMath theta task remains open until that semantic realization is replaced or justified by a phase-continuum construction independent of pre-existing trigonometric functions.

This plan fixes the implementation boundary between the newly observed phase-overlap coordinate and the already implemented finite Gauss-Wantzel-facing orbit layers.