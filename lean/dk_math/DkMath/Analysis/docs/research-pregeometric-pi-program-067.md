# Research Program 067: A Pre-Geometric Normalization Constant

## Purpose

This program investigates whether the constant later identified with
Euclidean pi can first be characterized without assuming a circle, an angle,
or polar coordinates.

The starting data are instead:

```text
an exact-order-four action
an affine filling of each discrete transition
a conserved quadratic quantity q2 at the endpoints
an exact scalar profile measuring departure from that boundary
reflection symmetry of the profile
refinement and normalization
```

The intention is not to redefine `Real.pi` prematurely. It is to construct an
independent normalization constant from the transition mechanism and
eventually prove a bridge theorem identifying it with `Real.pi`.

The Euclidean bridge now names the first external angle as
`semanticQuarterTurnAngle`. This value is definitionally `Real.pi / 2`, but
its role is deliberately interpretive: the algebraic four-state action is
constructed first, and the Euclidean model later reads one semantic action as
the angle `theta = pi / 2`. Thus the current theorem is an angle-reading
bridge, not a derivation of `pi`.

## Proven Starting Point

For a semantic core-zero kernel, one affine transition is

```text
E(z,t) = (1-t) z + t A(z).
```

Lean now verifies:

```text
q2(E(z,t)) = phaseDepth(t) q2(z),
phaseDepth(t) = (1-t)^2 + t^2,
phaseDepth(1-t) = phaseDepth(t),
phaseDepth(t) >= 1/2 > 0.
```

The same edge is transported through all four phases by action iteration.
Adjacent endpoints agree, and the edge family is periodic with phase index
four.

This is a continuous-symmetry precursor at the algebraic level: the state
path is oriented, but its scalar boundary-depth observation folds about the
midpoint.

## Strategic Interpretation

The current construction does not move along a circle. It moves along affine
segments and records exactly how far the quadratic boundary law fails between
the endpoints.

This gives the following research order:

```text
linear transition
  -> quadratic boundary defect
  -> reflection symmetry
  -> repeated refinement
  -> normalization factors
  -> limiting weight
  -> normalization constant
  -> comparison with Euclidean pi
```

Circular geometry is therefore a later model of an independently constructed
limit law. It is not used to generate the law.

## Why a Square Root May Appear

A one-dimensional Gaussian normalization has the form

```text
G = integral over Real of exp(-x^2).
```

Its square is naturally a two-coordinate quantity:

```text
G^2 = double integral of exp(-(x^2 + y^2)).
```

The present CF2D invariant is also quadratic in two coordinates. This makes
the distinction between a one-dimensional normalization constant and its
two-dimensional square structurally relevant.

This motivates, but does not yet prove, a future theorem of the form:

```text
transition normalization constant squared = Real.pi.
```

The square-root phenomenon must be derived from a dimension or product
theorem, not inserted as notation.

## Formal Milestones

### Milestone 0: first angle reading - implemented

`EuclideanPhase.lean` now packages the existing quarter-turn comparison as a
DkMath-named angle bridge:

```text
semanticQuarterTurnAngle = Real.pi / 2
semantic action = Euclidean rotation by semanticQuarterTurnAngle
```

This keeps the main line visible. Before a circle parameter or polar angle is
constructed, the boundary detector and the exact order-four action already
determine a transition with the same operational behavior as a Euclidean
quarter-turn. The standard Euclidean plane supplies the later interpretation
as `theta = pi / 2`.

### Milestone A: continuous four-edge loop - implemented

1. The real CF2D target carries the topology induced from `Real × Real`.
2. Each affine edge is packaged as a Mathlib `Path`.
3. Four seam-compatible paths are concatenated.
4. Core-zero exact order four closes the endpoint without Euclidean
   terminology.

### Milestone B: boundary normalization - implemented

1. The positive correction `1 / sqrt (phaseDepth t)` is defined and continuous.
2. The normalized master edge preserves the original `q2` value.
3. The normalized master edge is continuous and has the original endpoints.
4. All four action translates preserve the same boundary, meet at exact
   seams, and concatenate to a closed continuous path.
5. The closed path is packaged in the fixed `q2` level-set subtype, so
   boundary membership is enforced by the target type.

### Milestone C: refinement law

1. Define a finite partition of one affine phase, initially by the dyadic
   nodes `k / 2^n`.
2. Define the local boundary correction from the exact identity
   `q2 (semanticPhaseEdge r z t) = phaseDepth t * q2 z`.
3. Specify whether refinement composes corrections multiplicatively or,
   after taking logarithms, additively. This choice must be made by a proved
   composition law rather than by analogy with Gaussian normalization.
4. Prove the one-step refinement equation comparing level `n` with
   level `n + 1`.
5. Identify the centered quadratic term
   `2 * (t - 1/2)^2 + 1/2` as the exact local datum controlling any later
   asymptotic statement.

The first implementation checkpoint is deliberately finite: dyadic nodes,
their reflection symmetry, and a theorem stating how one subdivision level
refines the preceding level. No infinite product or Gaussian claim belongs
in that checkpoint.

This finite checkpoint is now implemented in `SemanticCF2DDyadic.lean`.
Even child indices recover their parent nodes exactly, while odd child
indices are the midpoints of adjacent parents. Complementary indices produce
the reflected parameter `1 - t`, and therefore have equal `phaseDepth`.

`SemanticCF2DRefinement.lean` now adds the first exact observation law.
Depth and normalization are inherited by even children and preserved by
reflection. At an odd child, the quadratic profile satisfies

```text
child depth
  = average of adjacent parent depths
    - 1 / (2 * (2^n)^2).
```

Thus the first refinement defect is an explicit positive inverse-square mesh
term. It is now named `dyadicPhaseDepthDefect`; its positivity proves that
every genuine odd child lies strictly below the adjacent-parent average.
There are exactly `2^n` such children, and their finite total defect is

```text
2^n * 1 / (2 * (2^n)^2) = 1 / (2 * 2^n).
```

This is an exact finite aggregation law. It does not yet assert convergence,
although its closed form exposes the scale that a later limit theorem must
analyze. The remaining task is to identify a mathematically justified
aggregate composition law for boundary normalization.

The elementary limit layer is now implemented separately in
`SemanticCF2DLimit.lean`. The defect introduced at one level has the exact
form `(1/2)^(n+1)` and tends to zero. However, the cumulative finite sum is

```text
sum over n < m = 1 - (1/2)^m,
```

so the full hierarchy tends to the normalized total one. This distinction is
structural: each new level becomes negligible, while all levels together
retain a nonzero conserved account. No Gaussian or `pi` interpretation is
attached to this geometric-series limit.

The first finite normalization-composition theorem is now implemented in
`SemanticCF2DComposition.lean`. At every sampled node,

```text
normalization^2 * depth = 1.
```

Multiplying this identity over the complete finite dyadic mesh gives

```text
(product normalization)^2 * product depth = 1.
```

Both finite products are strictly positive. This is an exact transport of the
pointwise boundary-restoration law through finite multiplication. It does not
yet identify either product as the canonical refinement observable, nor does
it justify an infinite product or logarithmic limit.

`SemanticCF2DLogComposition.lean` now records the equivalent finite additive
form. Pointwise positivity permits logarithms, and summation over the same
complete mesh gives

```text
2 * logNormalizationSum + logDepthSum = 0.
```

The two sums are proved equal to the logarithms of their respective finite
products. This equivalence supplies a comparison surface for later limit
selection; it does not select the raw sum, an average, or a weighted sum as
canonical.

The same module also records two scalar reweightings as finite candidate
observables. The uniform average divides by the number of complete-mesh nodes,
and the mesh-width version multiplies by `1 / 2^n`. In both cases, the
logarithmic cancellation law is transported exactly. These are not yet
canonical limit choices; they only make the candidate comparison surface
explicit before trapezoidal, midpoint, or other weighted observables are
tested.

The finite comparison surface now also contains the pointwise weighted
cancellation principle

```text
sum_k w_k * (2 log normalization_k + log depth_k) = 0.
```

This theorem separates the algebraic cancellation mechanism from the choice of
weights. The standard trapezoidal candidate is then implemented by giving the
two endpoints half a mesh width and every interior node one mesh width. This
is still a finite observable; it does not by itself prove convergence or
select the Gaussian-relevant normalization.

The weight totals are now part of the formal comparison. Uniform average and
trapezoidal weights both have total mass `1`. In contrast, the plain
mesh-width complete-node weights have total mass `1 + h_n`, exposing the
endpoint overcount that must be considered before treating that observable as
a closed-interval integration candidate.

There is a useful finite cancellation in this comparison. At both endpoints,
depth and normalization are equal to `1`, so their logarithmic observations
are zero. Consequently, the plain mesh-width and trapezoidal log-depth sums
are equal at every finite level, and the same is true for log-normalization.
Thus the two candidates differ as measures, but not on these particular
boundary-log observables. This distinction keeps the finite bookkeeping sharp
without prematurely selecting a canonical limit.

The general finite comparison is now explicit: for any sampled observable
`f`, the difference between the plain mesh-width complete-node sum and the
trapezoidal sum is

```text
h_n / 2 * (f 0 + f (2^n)).
```

The log-depth and log-normalization equalities are therefore special cases
where the endpoint values vanish. This theorem is intentionally finite; it
does not identify which weighted observable should survive refinement.

The endpoint-zero case is now packaged as a separate corollary. This keeps
future observables cleanly classified: endpoint-zero quantities inherit
mesh/trapezoid equality immediately, while centered quantities with nonzero
endpoint values must account for the endpoint correction.

The centered logarithmic correction now has its first finite quadratic
estimate. Lean proves

```text
centeredLogPhaseDepth(t) = log(1 + 4 * (t - 1/2)^2),
0 <= centeredLogPhaseDepth(t),
centeredLogPhaseDepth(t) <= 4 * (t - 1/2)^2.
```

These pointwise inequalities have been lifted to arbitrary nonnegative finite
weights on the dyadic mesh. Mesh-width, uniform-average, and trapezoidal
centered log-depth sums are therefore nonnegative and bounded above by their
corresponding finite centered quadratic moments. This is a finite estimate
only: it prepares the next moment calculation, but it does not yet assert a
closed form, a limiting integral, a Gaussian law, or a `pi` identification.

The first centered observable is now implemented. `centeredLogPhaseDepth`
subtracts the midpoint baseline `log(1/2)` from `log(phaseDepth t)`. It
vanishes at `t = 1/2`, has endpoint value `log 2`, and is identified with

```text
log (1 + 4 * (t - 1/2)^2).
```

On the complete dyadic mesh, the plain mesh-width centered log-depth sum and
the trapezoidal centered log-depth sum differ by exactly `h_n * log 2`. This
is the finite point where the endpoint correction reappears after centering.
It is a quadratic-profile bridge, not yet a Gaussian limit.

The pointwise quadratic comparison is also implemented:

```text
0 <= centeredLogPhaseDepth t
centeredLogPhaseDepth t <= 4 * (t - 1/2)^2
```

The first inequality follows because the centered quadratic profile is at
least `1`; the second is the `log(1 + x) <= x` comparison applied to
`x = 4 * (t - 1/2)^2`. This creates the finite bridge from logarithmic
correction accounting to quadratic moment estimates.

The first finite quadratic moment bound is also implemented. On the unit
interval, the centered quadratic profile satisfies

```text
4 * (t - 1/2)^2 <= 1.
```

Every complete dyadic node lies in that interval, and the trapezoidal weights
have total mass one, so Lean proves

```text
dyadicPhaseTrapezoidCenteredQuadraticSum n <= 1.
```

The exact finite value is now also proved:

```text
dyadicPhaseTrapezoidCenteredQuadraticSum n
  = 1/3 + 2/(3 * (2^n)^2).
```

Here `2^n` is Lean's `dyadicPhaseDenom n`. The code states the theorem with
`dyadicPhaseDenom n`, and the equality `dyadicPhaseDenom n = 2^n` is the
definition of the dyadic denominator.

The proof stays finite. It first evaluates the complete-node mesh-width
quadratic moment by elementary first-power and square-sum formulas, then
subtracts the trapezoidal endpoint correction. This exposes the finite
correction to the later `1/3` target without invoking an integral or a limit.

Combining this closed quadratic moment with the pointwise logarithmic upper
bound gives the finite centered log-depth estimate

```text
dyadicPhaseTrapezoidCenteredLogDepthSum n
  <= 1/3 + 2/(3 * (2^n)^2).
```

This is still only a finite inequality. It does not assert convergence of the
left-hand side.

The first DkMath limit vocabulary is now implemented in
`DkMath.Analysis.DkLimit`. It deliberately keeps Mathlib's filter semantics
under the hood, but gives DkMath names to the recurring collapse roles:

```text
DkTendstoAtTop
DkGapCollapsesTo
DkPuncturedGapCollapsesTo
```

This is an entrance, not a replacement for Mathlib analysis. It lets later
files state DkMath-shaped theorems while preserving a stable bridge to
`Filter.Tendsto`.

`SemanticCF2DLogLimit.lean` is the first use of that entrance in this
trigonometric route. Lean proves

```text
1/3 + 2/(3 * (2^n)^2) -> 1/3,
dyadicPhaseTrapezoidCenteredQuadraticSum n -> 1/3.
```

The second theorem follows from the finite closed form. This is still a
quadratic-control limit, not a centered log-depth limit. The log-depth limit
requires a matching lower estimate.

### Milestone D: limit and Gaussian bridge

1. Prove convergence of the refinement correction.
2. Determine whether its limiting weight is Gaussian.
3. Define the resulting normalization constant independently of `Real.pi`.
4. Compare it with the standard Gaussian integral in Mathlib.

### Milestone E: Euclidean identification

1. Interpret fixed `q2` boundaries as Euclidean circles.
2. Compare the normalized four-phase path with a standard circle
   parametrization.
3. Prove that the independently obtained normalization constant agrees with
   `Real.pi`.
4. Only then introduce an angular interpretation.

## Guardrails

The following claims are not established by the current implementation:

```text
repeated affine correction converges;
the limiting weight is Gaussian;
the resulting constant exists independently;
that constant equals Real.pi;
the affine four-edge loop itself is a circle.
```

The present result supplies a concrete quadratic and symmetric local
mechanism from which these theorem obligations can be investigated.

## Immediate Next Step

The coordinate-circle and standard `EuclideanSpace Real (Fin 2)` metric-sphere
bridges are now implemented, including the degenerate zero boundary. The next
interpretive step has also identified the core-zero action with the standard
coordinate quarter-turn linear isometry. After pulling back Mathlib's standard
complex orientation, that isometry is now proved equal to the oriented
rotation by `Real.pi / 2`. This remains an interpretation of the existing
boundary action, not an intrinsic derivation of `pi` and not a replacement
construction.
Refinement and limit arguments remain separate checkpoints.
