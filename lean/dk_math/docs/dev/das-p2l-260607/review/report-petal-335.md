# Petal / FloatWindow implementation report - checkpoint 335

## Result

Checkpoint 335 closes both requested branches without `sorry`.

The positive FIFO branch is now global rather than recursive-only: the owned
queue before any canonical block is exactly the newest upper tail of all
historical carry-two claims after deleting the cumulative *actual* consumed
count.  This yields exact source-age, deficit, maximum-age, minimax, and
conditional eventual-consumption theorems.

The negative finite-signature branch is also globalized.  The normalized
top-two enrichment fails at every lower-window depth `r >= 1`, and every finite
coarsening of that enrichment fails with it.  A separate exact audit proves
that normalized top-three data still fails at depth one.

No theorem here proves that a uniform source-age bound exists.  No theorem is
claimed for arbitrary upper-prefix length.

## Global source-owned FIFO normal form

The new module

```text
DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
```

defines the historical and cumulative carriers

```text
canonicalHistoricalClaimSourceCarrier
canonicalOwnedCumulativeConsumedClaimsBeforeBlock
canonicalCumulativeConsumedCountBeforeBlock.
```

Lean proves that consumed source carriers from distinct blocks are disjoint,
that a consumed identity never reappears in a later available or consumed
carrier, and that cumulative source cardinality equals cumulative scalar
actual consumption.

The exact historical partition is

```text
historical claims
  = cumulative consumed identities union outstanding owned identities,
```

with a disjoint union.  Its cardinal form agrees with both the scalar queue
and the existing demand prefix sum.

The central global theorem is

```text
canonicalOwnedOutstandingClaimsBeforeBlock n m
  = eraseOldestN
      (canonicalCumulativeConsumedCountBeforeBlock n m)
      (canonicalHistoricalClaimSourceCarrier n m).
```

The deletion count is actual consumption.  Unused service is not carried into
the normal form.

## Generic oldest-first threshold theorem

`OldestFirstQueue.lean` now proves the generic equivalence

```text
eraseOldestN c s subset filter (t <= .) s
  <->
card (eraseOldestN c s) <= card (filter (t <= .) s).
```

The reverse direction uses the fact that `eraseOldestN` is the newest upper
tail, including the empty-remainder case.  A uniqueness theorem also says
that a same-cardinality subset lying entirely in the complement of the
discarded lower prefix must be the FIFO remainder itself.

## Exact source-age characterizations

Using the global normal form and the generic threshold theorem, Lean proves

```text
CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
  <->
CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H.
```

Thus the earlier scalar cardinal condition is now an exact characterization
of actual FIFO source age, not merely a consequence of it.

The old-source carrier and signed deficit are also explicit:

```text
oldSourceClaims.card - cumulativeConsumed
  = outstandingQueue - recentSourceClaims.card
```

in `Int`, and

```text
owned source age <= H at block m
  <-> canonicalSourceAgeDeficit n H m <= 0.
```

The global version quantifies this condition over every canonical block.

## Oldest source, maximum age, and FIFO optimality

The API now contains

```text
canonicalOldestOutstandingSource
canonicalOwnedMaximumSourceAge
CanonicalAdmissibleOwnedRemainder.
```

The maximum age of an empty queue is explicitly zero.  Uniform actual source
age is equivalent to bounding this maximum age at every block.

For every admissible subset of historical claims having the scalar queue's
cardinality, FIFO maximizes the minimum retained source.  Equivalently, it
minimizes the maximum source age among source assignments realizing the same
scalar outstanding queue.  This is a comparison of assignments at one block;
it does not model an arbitrary alternative recursive policy.

## Conditional eventual consumption

Assuming a uniform actual source-age bound `H`, every source older than `H` is
absent from the owned queue.  Since every canonical block has positive length,
a source born in block `k` has a consuming block witness before

```text
k + H + 2.
```

This is a genuine source-to-consumption-block result, but remains conditional
on the uniform age hypothesis.  The existence of such an `H` is still the
primary positive Gap.

## Reusable projected-cycle obstruction

`FiniteSignedTransition.lean` now exposes generic positive projected-cycle
contradictions for both two and three realized edges.  Concrete source states
need not form an orbit cycle; only their projected endpoint signatures must
close, while their realized weights have positive total.

This isolates the exact logical obstruction:

```text
closed projected cycle + positive actual total weight
  -> no sound bounded-potential certificate covering those edges.
```

## Symbolic top-two obstruction at every depth

For every `r >= 1`, the symbolic sources are

```text
A_r = 7 * 2^(r + 2) - 1
B_r = 5 * 2^(r + 2) - 1.
```

Lean proves their first and second successor values, all six exact binary
widths, lower residues, heights, upper carries, normalized top-two words, and
width-growth flags.  The endpoint signatures close as

```text
signature (T A_r) = signature B_r
signature (T B_r) = signature A_r,
```

while the two realized signed-width weights are `+1` and `0`.

Therefore, for every `r >= 1`, no global bounded-potential certificate using

```text
FixedLowUpperBoundarySignature r
```

can cover all accelerated odd transitions.  The former `r = 1` witnesses
`55` and `39` remain as concrete regressions, and their obstruction theorem is
now a corollary of the depth-parametric result.

The same obstruction survives every finite factor

```text
f : FixedLowUpperBoundarySignature r -> Signature.
```

This rejects coarsenings only.  A strict refinement carrying genuinely new
upper information is outside the theorem.

## Top-three depth-one audit

The next enrichment retains normalized top-three bits.  At `r = 1`, Lean
proves the exact concrete transitions

```text
89 -> 67
39 -> 59
59 -> 89
```

with signed-width weights `0`, `0`, and `+1`.  It also proves every coordinate
needed for the nontrivial identification

```text
fixedLowUpperBoundaryThreeSignature 1 67
  = fixedLowUpperBoundaryThreeSignature 1 39.
```

The other two cycle links are exact concrete endpoint equalities.  Hence the
top-three depth-one observation also cannot support a global sound bounded
potential covering every accelerated odd edge.

This does not justify an arbitrary-prefix theorem.  It establishes one exact
three-bit obstruction and shows that adding one more normalized leading bit
does not by itself resolve the information loss.

## What is now fact

The following statements are formally established:

1. The recursive canonical owned queue is globally the newest historical
   upper tail after cumulative actual consumption.
2. FIFO source age `<= H`, recent-source cardinal coverage, nonpositive
   source-age deficit, and maximum source age `<= H` are equivalent views of
   the same condition.
3. FIFO is source-age optimal among same-cardinality assignments of historical
   claims.
4. A uniform source-age bound would force every source to be consumed within
   an explicit finite block lag.
5. Fixed-low plus normalized top-two data fails for every `r >= 1`, including
   every finite coarsening of that observation.
6. Fixed-low plus normalized top-three data fails at `r = 1`.

The remaining positive problem is not representation bookkeeping.  It is the
actual arithmetic theorem

```text
exists H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H.
```

Nothing in this checkpoint assumes or proves that statement.

## Verification

All changed Collatz/FloatWindow files contain no new `sorry`.

Successful build gates:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
```

## Suggested continuation

The next positive route should target `canonicalSourceAgeDeficit` directly.
The global queue theory has reduced actual age boundedness to the signed
inequality

```text
old source demand <= cumulative actual consumption.
```

A useful next checkpoint would search for an arithmetic amortization theorem
that controls this deficit without replacing actual consumption by total
service.

On the negative route, further upper-prefix experiments should first locate
and then exactly prove a projected cycle for each proposed strict refinement.
The top-three result alone must not be extrapolated to arbitrary prefix length.
