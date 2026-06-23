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
