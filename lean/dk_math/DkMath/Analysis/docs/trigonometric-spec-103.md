# DkMath Trigonometric Specification: Checkpoint 103

## Purpose

This note records the current DkMath interpretation of trigonometric
structure. It is a specification note, not a new proof target.

The main distinction is order of construction. Classical presentations often
start with a circle, an angle parameter, or analytic functions `sin` and
`cos`. The present DkMath route starts with:

```text
q2 boundary detector
core-zero semantic action
exact order four
finite phase table
continuous edge filling
normalization back to the q2 boundary
Euclidean reading
```

Thus the current formal object is a conserved action and its phase table. The
Euclidean angle is an interpretation attached afterward.

## Implemented Finite Phase Table

Let `A` be the transported semantic action under the core-zero hypothesis.
Lean now records the iterate table through
`semanticActIter r k z = (semanticAct r)^[k] z`.

The semantic layer proves:

```text
semanticActIter r k z = semanticActIter r (k % 4) z
```

The Euclidean bridge reads the four residues as:

```text
k % 4 = 0  ->  identity
k % 4 = 1  ->  quarter-turn
k % 4 = 2  ->  half-turn / negation
k % 4 = 3  ->  reverse quarter-turn
```

In the chosen Euclidean orientation this becomes:

```text
0        ->  0
1        ->  Real.pi / 2
2        ->  Real.pi
3        ->  3 * Real.pi / 2
```

This is the current DkMath `theta` reading:

```text
semantic action count k
  -> k % 4
  -> finite phase table
  -> Euclidean rotation by semanticPhaseAngle (k % 4)
```

## What This Does Not Claim

The current implementation does not claim:

```text
an intrinsic construction of Real.pi;
a continuous global angle coordinate;
a definition of DkMath sin and cos on all angles;
a Gaussian normalization theorem;
an equality between the refinement-limit constant and Real.pi.
```

The theorems involving `Real.pi` live in `EuclideanPhase.lean`. They are
external readings of a pre-existing order-four semantic action.

## DkMath Trigonometric Functions: Working Specification

The intended DkMath specification is:

```text
DkCos(theta) and DkSin(theta)
  are not introduced first as analytic functions.

They should be recovered from:
  1. the boundary-preserving normalized transition,
  2. a cyclic parameter obtained by gluing four normalized edges,
  3. the coordinate projections of that boundary action,
  4. a bridge proving agreement with Mathlib Real.cos and Real.sin.
```

At the finite table checkpoint, only the special values are represented by
action states:

```text
theta = 0           -> identity coordinates
theta = pi / 2      -> quarter-turn coordinates
theta = pi          -> negation coordinates
theta = 3*pi / 2    -> reverse quarter-turn coordinates
theta = 2*pi        -> identity coordinates
```

The continuous interpolation between these rows belongs to the next phase.

## Roadmap

The next proof directions are independent and should remain separate:

```text
1. Map-level wrappers
   Package the current pointwise modulo-four bridge as a map equality.

2. Continuous theta extraction
   Build a global cyclic parameter from the four normalized edges.

3. DkMath sin/cos definitions
   Define coordinate projections of the normalized cyclic action.

4. Euclidean bridge
   Prove that the DkMath coordinate projections agree with
   Mathlib's `Real.cos` and `Real.sin` under the Euclidean interpretation.

5. Intrinsic pi route
   Continue the refinement/log-depth/Gaussian route independently.
```

The key guardrail is that the finite order-four phase table is already
proved without circles, angles, or trigonometric functions. Euclidean
geometry explains how to read it, but does not generate it.
