# GNIP completion report — gnomon inversion/projection recovery campaign

## Status

**COMPLETE — READY FOR MERGE / LEGENDRE HANDOFF.**

The bounded goal of this branch was to recover the scattered square-gnomon arithmetic into a neutral source, connect it exactly to the degree-two Cosmic/GTail kernel, preserve Collatz compatibility, restate the Legendre square shell as an open unit gnomon, and determine whether the adjacent-shell transition carries a useful preservation law.

The final answer is:

```text
neutral gnomon growth        : recovered and generalized
Cosmic / GTail bridge        : exact
a pplication compatibility   : preserved
Legendre open-shell bridge   : exact
successor support transport  : false for the natural reindex
successor support firewall   : exact and nontrivial
historical real projection   : still a separate observer
Legendre conjecture          : not proved
```

## GNIP-000 — neutral algebra

Added the application-independent source:

```text
DkMath.Gnomon.Algebra
```

with

```text
oddGnomon n = 2*n+1
squareGnomonBand x u = u*(2*x+u)
petalMul a b = 2*a*b+a+b
```

and proved arbitrary-thickness square growth, composition, shifted unit decomposition, and square reconstruction.

The essential composition law is:

```text
squareGnomonBand x (u+v)
  = squareGnomonBand x u + squareGnomonBand (x+u) v.
```

## GNIP-001 — degree-two Cosmic bridge

Added:

```text
DkMath.Gnomon.CosmicBridge
```

and fixed the exact coordinate orientation:

```text
GTail 2 1 u x = 2*x+u
oddGnomon x = GTail 2 1 1 x
squareGnomonBand x u = u * GTail 2 1 u x.
```

The square-growth theorem is derived through the existing production Cosmic identity rather than by duplicating the polynomial proof.

## GNIP-002 — Collatz recovery

Refactored `DkMath.Collatz.GnomonEvaluation` so that

```text
OddGnomonLayer n
```

uses `DkMath.Gnomon.oddGnomon` as its source of truth while retaining the existing Collatz public theorem names and all Collatz-specific valuation/dynamics definitions.

## GNIP-003 — Legendre open unit-gnomon bridge

Added:

```text
DkMath.NumberTheory.Legendre.GnomonBridge
```

and proved the exact coordinate identities

```text
SquareOffset n r
  <-> 1 <= r and r < oddGnomon n

squareOffsets n
  = Finset.Ico 1 (oddGnomon n).
```

Thus the open interval between consecutive squares is exactly the open interior of one unit square-gnomon layer.

The existing `LegendreConjecture` and `SquareAnchoredSupportEscape` are also restated exactly in these coordinates, without adding a provider or existence theorem.

## GNIP-004 — successor firewall

Added:

```text
DkMath.NumberTheory.Legendre.GnomonSuccessor
```

The successor shell has two more seats, while a fresh threshold prime controls exactly the two threshold offsets in the prime-threshold case.  Removing those seats restores the old shell cardinality.

The natural threshold-skipping reindex does **not** preserve old-prime coverage.  Concrete `30 -> 31` mismatches are kernel-checked in both directions.

The main new structural theorem is the common-support firewall:

```text
q | n^2+r
q | (n+1)^2+r
-----------------
q | oddGnomon n.
```

For the canonical threshold-skipping reindex this becomes:

```text
lower region common support -> q | oddGnomon n
upper region common support -> q | 2*(n+1).
```

At `30 -> 31` this means:

```text
lower region -> common old prime must divide 61 -> none for q <= 30
upper region -> common old prime must divide 62 = 2*31 -> only q=2 can remain
```

This is an anti-preservation / persistence-firewall law, not a full-cover theorem.

## Historical inversion projection

The older real sample API is present at:

```text
DkMath/Samples/Projection.lean
namespace DkMath.Cosmic
```

with `Pi`, `U`, and `cosmicProjection_gap_eq`.

No exact production bridge currently identifies that continuous real projection with the discrete finite successor-support firewall.  The two should remain separate until a mathematically justified bridge is found.

## Why this campaign stops here

A further exact support-intersection API is possible, but it would no longer answer the recovery/inversion question.  To turn the firewall into full-cover failure, one must control how support labels hand off between different prime directions across the successor reindex.

That requires the existing Legendre machinery around:

```text
OldSupportGcd
FreshCollisionMatching
support/capacity modules
full-cover frontier
```

Therefore the next research step is application-owned Legendre work, not another generic GNIP checkpoint.

## Handoff

After merge:

```text
1. resume Legendre from current develop
2. treat GnomonSuccessor firewall as a new input
3. investigate support handoff / collision / capacity under the canonical reindex
4. stop if it reduces to existing matching/capacity bounds without new leverage
5. after the Legendre route is classified, return to the ABC branch
```

## Scope statement

This branch does **not** prove:

```text
LegendreConjecture
SquareAnchoredSupportEscape
not (SquareOffsetsFullyCovered n)
full-cover propagation between adjacent shells
an exact bridge to the historical real inversion projection
```

It does prove a new exact structural obstruction controlling which prime directions may persist across adjacent square-growth coordinates.
