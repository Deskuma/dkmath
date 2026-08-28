# PUU-L033 Positive-Offset First-Hit / Anchor-Seat Exclusion Audit

## Scope

This checkpoint stays provider-side.  It removes the anchor seat `t = 0`
from the finite cyclic first-hit statistic of PUU-L032 and compares arbitrary
wheel labels with labels reached by square anchors.  No `2*n` width,
`SquareCell`, `SquareOffset`, escape theorem, primality claim, Jacobsthal
machinery, or Legendre consumer was added.

## Implemented API

The new module
`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetPositiveFirstHitAudit`
defines `genericPositiveUnreservedOffsetProfile` over
`Finset.Icc 1 (finitePrimeBasisProduct S)`.  Its `min'` defines
`genericFirstPositiveUnreservedOffset`; the public API proves:

- strict positivity;
- the upper bound by one full period, allowing equality with the period;
- landing on an `IsPrimeBasisWheelSurvivor`;
- minimality among strictly positive smaller offsets.

The square-anchor coordinate
`squareAnchorFirstPositiveUnreservedOffset` is definitionally the generic
coordinate at `squareAnchorWheelProjection S n`.  The module exposes the
generic bridge, positivity, period bound, survivor, minimality, and same-phase
invariance theorems.  It also defines
`genericPositiveFirstHitRadius` and `squarePositiveFirstHitRadius`, proves
the square-restricted radius inequality, and exposes the pointwise square
bound.

The positive-profile nonemptiness proof reuses the public L032 generic
profile nonemptiness theorem: a zero witness is replaced by one full period,
so the positive search remains valid even when the first positive return is
exactly `M`.

## Exact regressions

The public profile membership and finite-minimality API proves:

| basis `S` | period `M` | generic positive radius | square positive radius | witness |
|---|---:|---:|---:|---|
| `{2,3}` | `6` | `4` | `4` | phase `A=1`, anchor `n=1`, next survivor `5` |
| `{2,3,5}` | `30` | `6` | `6` | phase `A=1`, anchor `n=1`, next survivor `7` |

The exported regression theorems also record the phase projection
`squareAnchorWheelProjection S 1 = 1` and the corresponding positive first-hit
value (`4` and `6`).

## Verdict

**Outcome B — ANCHOR-SEAT-GAIN-COLLAPSES.**

The square-phase restriction remains a genuine restriction of the whole
cyclic survivor profile, but it does not improve the worst forward positive
first hit in either required regression.  The earlier L032 strict gain was
therefore caused by allowing the anchor seat `t = 0` in the statistic; after
excluding that seat, square-phase-alone first-hit refinement is closed as an
independent obstruction source.

The next checkpoint should introduce a genuinely independent coupling, such
as successor-pair dynamics or basis growth, and should use this positive
offset statistic.

## Validation

Validated with:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetPositiveFirstHitAudit
```

The target completed successfully, including the imported dependency graph.
The new module was exported through
`DkMath.NumberTheory.PrimorialUniverse`, whose module docstring now records the
positive-offset boundary and the two equality regressions.
