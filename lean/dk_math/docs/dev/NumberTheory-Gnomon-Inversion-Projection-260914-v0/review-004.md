# review-004 — GNIP-004 successor gnomon firewall

## Verdict

**APPROVED — Outcome A: STRUCTURAL FIREWALL FOUND.**

GNIP-004 isolates a genuinely new cross-anchor obstruction.  The result is not a support-preserving successor map; it proves the opposite kind of structure: common prime support across the canonical successor reindex is forced into the prime divisors of the exact displacement.

## 1. Exact finite balance

The implementation proves

```text
card (squareOffsets (n+1)) = card (squareOffsets n) + 2
```

and defines the two threshold seats

```text
{n+1, 2*(n+1)}.
```

Removing them from the successor shell restores the old shell cardinality exactly.

Under `Nat.Prime (n+1)`, the existing `PrimorialWheelSuccessor` theorem identifies exactly those two seats with reservation by the new threshold prime.  This is a genuine exact balance, but by itself it is only cardinal bookkeeping.

## 2. Canonical reindex is not support preserving

The candidate

```text
successorThresholdInsert n r :=
  if r < n+1 then r else r+1
```

lands every old square offset in the threshold-removed successor shell.

The `30 -> 31` regressions prove both failure directions:

```text
r=6 : covered -> unreserved
r=7 : unreserved -> covered
```

Therefore the equal-cardinality shells cannot be interpreted as carrying the same old-prime support pattern under this canonical coordinate map.

## 3. New structural theorem

The key theorem is

```text
dvd_oddGnomon_of_dvd_adjacent_square_points
```

which proves

```text
q | n^2+r
q | (n+1)^2+r
-----------------
q | oddGnomon n
```

from the exact additive displacement

```text
(n+1)^2+r = (n^2+r) + oddGnomon n.
```

The lower/upper canonical-reindex split sharpens this to:

```text
lower region common support -> q | oddGnomon n
upper region common support -> q | 2*(n+1).
```

This is a useful anti-preservation firewall: the gnomon increment does not preserve the support labels; it constrains which labels can survive unchanged.

## 4. 30 -> 31 consequence

At `n=30`:

```text
oddGnomon 30 = 61
2*(30+1) = 62 = 2*31.
```

For old primes `q <= 30`, the lower region admits no persistent old prime channel because a common channel would have to divide the prime `61`.

In the upper region a common channel must divide `62`; among old primes `<=30`, only `2` is possible.  The production theorem currently exports the divisor statement `q | 62`; the final prime-specialized `q=2` corollary is not necessary for approval.

## 5. Relation to prior stop-route audit

This does not contradict the 2026-08-25 conclusion that the raw point rewrite into an extended offset window gives no shell transport.  GNIP-004 uses a different construction: equal-cardinality threshold removal plus a canonical threshold-skipping reindex, followed by an exact displacement analysis.

The resulting theorem is not a transport theorem.  It is precisely the missing firewall statement that the prior audit did not supply.

## 6. Relation to historical inversion projection

The historical real sample API lives in

```text
DkMath/Samples/Projection.lean
namespace DkMath.Cosmic
```

with `Pi`, `U`, and `cosmicProjection_gap_eq`.

No exact theorem currently connects that real observer to the discrete successor-support firewall.  Treat them as separate observers for now; do not force a real/rational bridge into this campaign.

## 7. Route judgment

No GNIP-005 is required on this branch.

A finite support-intersection theorem could be derived from the firewall, but converting that into a contradiction requires controlling support handoffs, collisions, and capacity across many seats.  Those concepts already belong to the Legendre application stack (`OldSupportGcd`, `FreshCollisionMatching`, capacity modules, and the full-cover frontier).

Therefore the correct handoff is:

```text
GNIP recovery/generalization campaign: COMPLETE
    -> merge infrastructure
    -> resume Legendre
    -> use GnomonSuccessor firewall as a new Legendre input
```

This campaign does not prove Legendre's conjecture and does not establish full-cover failure.
