# RH-CFBRC moving-line collision route

Date: 2026-08-05

Branch:

```text
wip/RH-CFBRC-moving-line-collision-260805-v0
```

## Purpose

The previous spectral-gauge audit route is closed.  This route studies a
nonzero normalized endpoint carrier constrained by two different geometries:

```text
local pair-index moving real line
+
external k-independent global real line
```

Projective two-scale nonresonance is intended to make these simultaneous
constraints incompatible at a nonreal off-critical zero.

## Exact first-stage Core

```text
EtaCriticalMirrorPairedFrameMovingRealLine
```

provides:

```text
complexRealLine
complexRealAxis
etaPairMovingRealLine
etaPairMovingRealLineDefect
etaPairMovingRealLine_add_real
etaPairMovingRealLine_add_imag_mem_iff
etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis
```

## Research beacons intentionally marked by sorry

```text
etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock
etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse
etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision
standardZetaRealAxisClosure_research_goal
etaCriticalMirrorEndpointGlobalZeroLineLock_research_goal
```

The top-level laboratory target is:

```text
riemannHypothesis_movingLineCollision_research_goal
```

It is not a completed RH proof.  It is deliberately dependent on the visible
`sorry` markers above.

## Final two external obligations

```text
1. EtaCriticalMirrorGlobalZeroLineLock
2. StandardZetaRealAxisClosure
```

The global direction must not be defined from the endpoint carrier itself and
must not contain `s.re = 1 / 2`, endpoint collapse, or an RH-equivalent premise.
A later completed-zeta / Hardy-frame audit must supply it externally.

## Same-object audit

The carrier used by the local and global locks is exactly:

```text
etaCriticalMirrorDominantNormalizedEndpointCarrier
```

No replacement by a mirror carrier, conjugate carrier, or a differently
indexed sequence is permitted in the final collision theorem.
