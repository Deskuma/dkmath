# Petal / Collatz implementation report: cp-313

## Status

`UniversalPaymentPressure.lean` now closes the finite pressure-accounting layer
over the canonical universal payment-block family.  The implementation remains
`sorry`-free.  The branch stops at a genuine ordered matching problem, rather
than at another partition or reindexing task.

## Implemented module

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
```

It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.

## Lean-certified facts

### 1. Honest local pressure fibers

The recovery and continuation objects are actual filtered `Finset`s inside a
canonical block.  Their membership theorems expose the existing
`OrbitDepthRecoversExactlyAt` and `OrbitDepthContinuesBeyond` predicates.

### 2. A canonical block is an exact depth staircase

For every source time `i` in block `k`,

```text
orbitExactDepth n i = paymentEndpointSeq n k - i + 1.
```

Consequently, a block of length `L` contains exactly one recovery incidence at
each depth `1, ..., L`, and no recovery incidence at depth zero:

```text
card recovery(k,d) = if 1 <= d and d <= L then 1 else 0.
```

### 3. Continuation has an exact closed count

The continuation fiber at depth `d` has cardinality

```text
card continuation(k,d) = L - d.
```

At depth zero this is the whole block.  When `d < L`, the fiber is the initial
closed interval ending at `endpoint - d`.  The interval theorem intentionally
requires `d < L`: without that hypothesis, natural-number truncated subtraction
can manufacture a false endpoint at zero even though the real fiber is empty.

### 4. Local signed pressure is fully classified

The actual local contribution is

```text
continuation card - recovery card
  = (L - d) - if 1 <= d and d <= L then 1 else 0.
```

For positive `d`:

```text
L < d      ->  0
L = d      -> -1
L = d + 1  ->  0
d + 2 <= L ->  L - d - 1
```

Thus local pressure is not uniformly nonpositive.  Long blocks can contribute
positive pressure at shallow depths.  A global sign theorem cannot be obtained
by proving every local block nonpositive.

### 5. Existing pressure counts are exactly the block sums

The existing `List.range` counts were converted to actual filtered initial
`Finset`s.  The canonical prefix is exactly

```text
Finset.range (paymentEndpointSeq n m + 1),
```

and filtering commutes with its disjoint block decomposition at card level.
Therefore both recovery and continuation counts split over the first `m + 1`
canonical blocks.  In particular:

```text
SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d
  = sum k in range (m + 1), blockPressureContributionInt n k d.
```

This is the direct bridge from the new staircase calculation to the established
pressure API.

### 6. Delayed debts have injective depth addresses

Every delayed debt source in block `k` is marked by

```text
canonicalPaymentDebtDepth n k i = endpoint(k) - i + 1.
```

This address equals `orbitExactDepth n i`.  Distinct delayed debt sources in
one block have distinct depth addresses, so the marked-depth image has exactly
the delayed-debt cardinality.

### 7. Capacity is represented by actual slots

The endpoint capacity carrier is

```text
Finset.range (extraPaymentCapacityAt n (paymentEndpointSeq n k)),
```

whose card is definitionally the endpoint capacity.  Immediate endpoint claims
remain separate from delayed debt claims.

### 8. The exact sign frontier is now named

`CanonicalEndpointPrefixCapacityDominance n m` states that every prefix through
`m` has at least as much cumulative endpoint capacity as cumulative delayed and
immediate claims.  Lean proves this equivalent to nonpositivity of every prefix
sum of `endpointAccountingTerm`.

An honest carrier-level target,
`CanonicalEndpointOrderedCapacityMatching`, asks for an injective payment map
from claims to capacity slots, with every slot occurring no later than its
claim endpoint.  Its existence is not asserted.

## Conditional consequence

If prefix capacity dominance is supplied, Lean proves

```text
bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 <= bitWidth n.1.
```

The global dominance predicate gives this bound for every canonical endpoint.
This is a conditional endpoint-boundedness theorem only.  It is not a proof of
convergence, nor by itself a proof of eventual periodicity.

## Genuine obstruction

All finite partitioning, staircase counting, list-to-Finset conversion, and
pressure summation requested in cp-313 are complete.  The remaining theorem is
structural:

```text
cumulative delayed claims + cumulative immediate claims
  <= cumulative endpoint capacity.
```

Equivalently, one must construct the ordered capacity matching, or derive its
prefix inequalities from a new orbit rule.  Cardinality algebra alone cannot
choose the payment destination of a claim across endpoint blocks.

## Next implementation direction

1. Inspect how `extraPaymentCapacityAt` changes between consecutive canonical
   endpoints and whether a delayed debt depth determines a canonical capacity
   slot.
2. Attempt a monotone greedy matching on the explicit claim and capacity
   carriers.
3. If greedy matching fails, formalize the first minimal prefix where claims
   exceed capacity and extract the resulting rigidity/overload witness.
4. Only after global dominance is established, build the finite-state argument
   needed for endpoint-state recurrence.  Do not infer eventual periodicity
   from bounded bit width without a deterministic endpoint transition theorem.
5. Keep strict decay, zero-drift-family classification, and cycle exclusion as
   separate downstream branches.

## Verification

The final build gate for this checkpoint is recorded in the completion message.

