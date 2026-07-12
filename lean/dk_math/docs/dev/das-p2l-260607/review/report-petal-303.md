# cp-303: Payment-block reindexing foundations

## Added facts

`PaymentBlockBridge` now exposes the first exact reindexing primitives:

```text
orbitWindowHeight (iterateT a n) t = orbitWindowHeight n (a + t)
iterateT (a + len) n = iterateT len (iterateT a n)
```

It also defines `extraPaymentCapacityOn` for a finite set of global orbit
indices and proves the endpoint arithmetic for a debt-supported block:

```text
a + (j + 1 - a) = j + 1
Ico a (a + (j + 1 - a)) = Icc a j
```

where `a = floatPaymentBlockStart n j h`.

## Current boundary

The shifted width ledger is proven.  The remaining central block balance needs
two finite reindexing identities: transport the recursive carry-two prefix
count to the global `Icc a j` filter, and transport `sumExtraHeight` to
`extraPaymentCapacityOn` over the same interval.  These are not semantic
gaps; they are explicit finite-sum/card transport lemmas.

No overload-to-width conclusion is asserted before those two identities are
available.  The code continues to distinguish a debt-supported suffix from a
future maximal height-one staircase.

## Verification

`PaymentBlockBridge` builds after these additions.  The final module and
top-level build gates are run as part of the checkpoint handoff.
