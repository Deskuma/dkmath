# Petal / FloatWindow implementation report - checkpoint 323

## Result

Stages A-G of the revised residual program are implemented in
`UniversalPaymentAmplitude.lean`.  The branch now reaches an actual
source-bearing residual incidence carrier.  All additions are no-sorry.

## Sliding pressure bridge

The previously missing prefix-difference API is closed:

```text
pressure at block start q
  = sum of block contributions on range q

window pressure q..m
  = pressure after endpoint m - pressure at block start q.
```

The zero source window has pressure zero, and the `q = 0` specialization
recovers endpoint-prefix pressure exactly.  Relative window pressure is still
kept distinct from an absolute `IsSourcePressureDepth` hypothesis.

## Actual block window

`canonicalPaymentBlockWindow n q m` is the union of canonical blocks indexed
by `Icc q m`.  For `q <= m`, Lean proves both normal forms:

```text
Icc (canonicalBlockStartTime n q) (paymentEndpointSeq n m)

range (paymentEndpointSeq n m + 1)
  \ range (canonicalBlockStartTime n q).
```

Generic filtered cardinality decomposes over the disjoint blocks.  Actual
continuation and exact-recovery source finsets are defined from this window,
and their signed cardinal difference equals the sliding pressure sum.

## Structural separation fact

For an active selected block at selected depth `d`, Lean proves

```text
d + 2 <= canonicalPaymentBlockLength n k.
```

Therefore active selected blocks at depth `d` are disjoint from blocks whose
length is exactly `d`.  Exact-length service at a selected depth necessarily
comes from a different block; it is not a token emitted by the selected block
itself.

## Residual terminology

`canonicalSelectedResidualCount` remains for compatibility.  The explicit
alias `canonicalUnorderedSelectedCarrierResidualCount` records its real
meaning: natural cardinal subtraction after granting unrestricted same-depth
tokens.  Its `Fin` carrier has no source-time or block coordinate and no causal
interpretation.

## Actual drift image

For every positive nonsaturated block, positive drift units now embed directly
into selected source incidences of that same block.  The finite image:

- has cardinality exactly `Int.toNat endpointAccountingTerm`;
- is contained in the selected source carrier by construction;
- is empty outside the positive nonsaturated branch.

`CanonicalSelectedDriftBucketCarrier` retains selected depth, block index, and
source time.  Its unordered residual is bounded by the older selected-carrier
residual, proving that the latter is a safe but potentially coarse bound caused
by unused selected-carrier slack.

## Actual residual incidence carrier

When exact-length token count does not exceed drift-image count, a
noncanonical unordered injection is chosen and its image is removed.  In the
opposite cardinal branch the residual is empty.  The resulting
`CanonicalActualSelectedDriftResidualCarrier`:

- embeds into the actual drift-image bucket;
- retains depth, block, and source coordinates;
- has cardinality exactly the unordered drift residual.

This is an actual incidence subset, but the matching remains unordered and is
not future-payment allocation.

## Safe stopping boundary

Stage H requires a fixed-depth causal queue.  The existing scalar Lindley
theorems are specialized to `canonicalBlockClaimCount` and
`canonicalBlockCapacityCount`; they cannot be instantiated with the new
depthwise arrivals and exact-length service.

The next safe implementation is a generic finite Nat-valued reflected queue
API, or a parallel fixed-depth specialization, proving the suffix-maximum
Lindley identity.  Only after that should unordered drift residual be compared
with causal queue residual.  No causal repayment or temporal Hall conclusion
is claimed at checkpoint 323.

## Next implementation

1. Extract a generic local reflected queue parameterized by arrivals and
   service.
2. Prove its terminal value equals the maximum positive suffix imbalance.
3. Instantiate arrivals with per-block selected drift-image cardinality at
   depth `d` and service with the exact-length indicator.
4. Prove unordered residual is bounded by the causal queue.
5. Add the temporal interval-order Hall theorem only after the queue surface is
   stable.
