# Petal / FloatWindow implementation report - checkpoint 331

## Result

The remaining amortization overrestriction has been removed.  Uniformly
bounded cumulative inflow is sufficient but not necessary for a bounded
queue.  The correct generic control is bounded cumulative net inflow after
outflow is retained.

This checkpoint also constructs the exact canonical scalar balance, connects
the existing finite signed-transition certificate to canonical windows and
queue bounds, and proves a generic bounded repayment-lag theorem.

## Strong balance telescope

The generic structure is now named `FiniteAmortizedBalance`, with neutral
fields `inflow` and `outflow`.  The old resource name remains an alias only.
Lean proves the full telescope:

```text
queue m + potential m + sum(outflow, range m)
  <= queue 0 + potential 0 + sum(inflow, range m).
```

Consequently, if

```text
sum(inflow, range m) <= sum(outflow, range m) + B
```

for every prefix, then

```text
queue m <= queue 0 + potential 0 + B.
```

Only the initial potential is used.

## Stable-throughput regression

Lean verifies the abstract transition

```text
queue = 0, potential = 0, outflow = 1, inflow = 1.
```

Its conservation law is exact and its queue is uniformly zero, while no
finite constant bounds all cumulative inflow sums.  This formally disproves
the necessity of bounded total inflow for queue stability.

## Exact canonical scalar balance

`canonicalQueueFiniteAmortizedBalance n` uses:

```text
queue     = queue before block
potential = 0
outflow   = actual consumed service
inflow    = block demand.
```

The exact reflected-queue identity proves its step law.  Unused service is
also explicit, with the proved scalar identities:

```text
consumed <= service
consumed <= queueBefore + demand
service = consumed + unusedService
queueAfter = queueBefore + demand - consumed.
```

These are scalar accounting facts and do not assert claim ownership.

## Finite signed-transition route

The relational certificate now has a canonical application theorem.  Given a
fixed finite signature certificate whose relation contains every edge
`k -> k+1` and whose actual edge weight is exactly
`endpointAccountingTerm n k`, Lean proves:

```text
every canonical window drift <= certificate.bound
canonical outstanding queue <= certificate.bound
canonical endpoint width <= bitWidth n + certificate.bound.
```

The first missing Collatz theorem on this route is a concrete finite signature
with a sound projected upper edge weight and bounded potential.  Existing
low-bit collision evidence rules out exact deterministic recovery, but does
not by itself rule out a nondeterministic upper-weight projection.

## Bounded repayment-lag route

`BoundedRepaymentLag.lean` proves the generic implication:

```text
all outstanding work lies among the previous L arrival slots
each slot creates at most A arrivals
------------------------------------------------------------
queue m <= L * A.
```

The first missing Collatz theorem is a uniform lag for all actual canonical
claims.  Current saturated-successor results repay selected local subclasses,
but do not provide such a global lag.

## Owned-carrier route

The first missing theorem remains a recursive source-bearing claim carrier
whose consumption preserves source identity and temporal nonreuse, and whose
cardinality agrees with the scalar reflected queue.  No such existence claim
is made in this checkpoint.

## Route comparison

The three noncircular routes are now separate:

1. finite signed transition: missing a sound finite canonical signature;
2. bounded repayment lag: missing a uniform canonical claim-lag theorem;
3. owned upper resource: missing a temporally coherent recursive carrier.

None is currently proved uniquely necessary.  The first route now has the
shortest complete conditional chain to endpoint width; the latter two retain
more claim-level information if their Collatz-specific obligations can be
proved.

## Verification

All required gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath
git diff --check
```

All changed FloatWindow Lean files remain free of `sorry` and local heartbeat
overrides.
