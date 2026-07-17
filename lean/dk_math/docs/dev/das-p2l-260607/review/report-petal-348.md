# Petal / FloatWindow Report cp-348

## Scope

This checkpoint constructed the honest arrival carrier for internal zero-spare
predecessor tokens.  It does not discharge the zero-spare residual and does not
change the current queue inequality.

Only `CanonicalExcursionOwnership.lean` was modified.

## Implemented Surface

The zero-spare predecessor support now has an explicit successor-block image:

```text
canonicalInternalZeroSpareSuccessorIndices n q m
```

with the membership and cardinality facts:

```text
mem_canonicalInternalZeroSpareSuccessorIndices
card_canonicalInternalZeroSpareSuccessorIndices_eq_zeroSpare
```

The targeted selected-arrival carrier is:

```text
CanonicalInternalZeroSpareSelectedCarrier n q m
```

It is indexed only by successor blocks coming from
`canonicalInternalSaturatedZeroSpareIndices n q m`.  It does not include
arbitrary zero-drift blocks.

## Charge And Embedding

Each internal zero-spare predecessor token is charged to an actual selected
spare incidence in its own successor block:

```text
canonicalInternalZeroSpareCharge
canonicalInternalZeroSpareCharge_fst
canonicalInternalZeroSpareCharge_successor_endpoint_zero
canonicalInternalZeroSpareCharge_mem_spare
```

The map was upgraded to a block-preserving embedding:

```text
canonicalInternalZeroSpareChargeEmbedding
```

and the cardinality certificate is:

```text
card_canonicalInternalSaturatedZeroSpareIndices_le_zeroSpareSelectedCarrier
```

## Fact Established

Every internal zero-spare predecessor token has a concrete selected spare
incidence in its zero-drift successor block, and these predecessor tokens
inject into the targeted selected-arrival carrier by their retained successor
coordinate.

This proves ownership of the zero-spare arrival surface as a finite incidence
certificate.  It still does not prove payment, discharge, orbit-wide
convergence, or removal of `internalZeroSpareCount` from the queue bound.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

All gates passed.  The modified ownership file adds no `sorry`.

## Next Implementation Inference

The zero-spare branch now has a precise owned-arrival carrier.  The next honest
step is not to remove the residual immediately, but to connect this carrier to
a service or repayment surface that explains when the selected zero-drift
arrival becomes usable by the queue accounting.  That requires a separate
local source theorem; this checkpoint intentionally stops before introducing
such a recurrence or framework.
