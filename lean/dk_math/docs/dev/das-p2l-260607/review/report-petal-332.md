# Petal / FloatWindow implementation report - checkpoint 332

## Result

This checkpoint repairs the repayment-lag window, strengthens canonical scalar
accounting to an exact prefix identity, and exposes a canonical finite signed
projection certificate with no arbitrary actual-weight bookkeeping.

The branch stops at an honest obstruction: no uniform canonical recent-demand
window bound is currently proved, and no proposed finite block signature has
yet established edgewise boundedness.  Consequently neither route may be
reported as an unconditional endpoint-width theorem.

## Exact recent-arrival window

The corrected window is

```text
recentArrivalMass arrivals L m
  = sum k in [m-L,m), arrivals k.
```

It contains no future index.  Lean proves that it is the full prefix when
`m < L`, the expected shifted range when `L <= m`, and has at most `L` slots.
Regressions cover `m = 0`, `m < L`, `m = L`, and `L = 0`.

The old `OutstandingQueueHasRepaymentLag` remains only as a deprecated coarse
compatibility predicate.  New callers use
`OutstandingBeforeQueueCoveredByRecentArrivals`.

## What lag actually proves

Lag coverage alone is not a queue bound.  Lean now separates the required
second obligation:

```text
queue covered by recent L arrivals
+ each arrival slot <= A
----------------------------------
queue m <= L * A
```

Alternatively, a direct recent-window mass bound `B` yields `queue m <= B`.
For the canonical queue these become two conditional interfaces.  No uniform
canonical `L`, `A`, or `B` is claimed.

## Exact canonical prefix balance

The block conservation identity telescopes exactly to

```text
canonicalQueueBefore m + sum(consumed, range m)
  = sum(demand, range m).
```

Hence the reflected queue is exactly cumulative demand minus cumulative
consumption.  This confirms that bounded total demand is unnecessary; bounded
net inflow is the relevant scalar quantity.

## Canonical finite signed projection

`CanonicalFiniteSignedTransitionPotentialCertificate` specializes the generic
relational certificate to the actual edge

```text
k -> k + 1
weight = endpointAccountingTerm n k.
```

A constructor supplies only a finite signature, a projected upper edge weight,
a bounded potential, and proofs that concrete edges lie below projected edges
and projected edges lie below potential differences.  Lean then derives:

```text
canonical queue <= certificate.bound
canonical endpoint width <= bitWidth n + certificate.bound.
```

Before any potential search, every candidate signature must prove that all
realized concrete edges sharing a signature pair have a finite common upper
bound.  Exact drift collisions are not themselves fatal; unbounded positive
collisions are.

## Route status

The current conditional routes are:

1. finite signed transition: the shortest complete conditional chain, missing
   a concrete finite signature with edgewise boundedness and a potential;
2. bounded repayment lag: missing both canonical lag coverage and recent-demand
   mass control;
3. owned claim carrier: potentially useful for source identity, claim age, and
   lag, but not assumed to be an initial finite upper resource;
4. raw-step projection: still a legitimate fallback if block signatures fail,
   but no uncontrolled-cycle claim has been made.

The first applicable stopping condition is therefore the absence of a proved
canonical recent-window demand bound.  Candidate signature auditing cannot
soundly advance to cycle or potential search until its independent edgewise
boundedness obligation is established.

## Verification

The targeted modules were checked first:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
```

The complete gate passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath
git diff --check
```

The changed FloatWindow Lean files contain no `sorry` and no local heartbeat
override.
