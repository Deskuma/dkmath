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

1. Define dyadic or rational subdivision of an affine phase.
2. Express the total correction as a finite product or sum of logarithms.
3. Prove compatibility under refinement.
4. Identify the exact local quadratic term controlling the limit.

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

The next bridge may identify positive real `q2` level sets with a standard
Euclidean metric sphere. The coordinate-circle homeomorphism is now
implemented, including the degenerate zero boundary; the remaining bridge is
to `EuclideanSpace Real (Fin 2)`. It must remain an interpretation of the
existing boundary path, not a replacement construction. Refinement and limit
arguments remain separate checkpoints.
