# cp-309 Direct Universal Payment-Block Ledger

## Main Result

The exact width ledger is now proved directly for every nonempty universal
payment block.  It does not assume a nonempty delayed Float-growth debt fiber.

For universal start `b` and endpoint `j`, Lean proves:

```text
bitWidth(iterateT(j + 1)) + extraPaymentCapacityAt(j)
  =
bitWidth(iterateT(b)) + card(carryTwoPaymentClaimFiberAt(j))
```

This is the correct block-local accounting surface for all extra-height
endpoints, including blocks with no delayed carry-two growth debt.

## Transport Chain

The proof combines three direct universal identities:

1. The shifted interval `[b, b + len)` equals `Icc(b, j)` for
   `len = j + 1 - b`.
2. The shifted carry-two count equals the complete carry-two claim-fiber card.
3. The shifted extra-height capacity equals the endpoint capacity.

The generic shifted width ledger then closes the equality without passing
through the delayed-growth-debt suffix.

## Signed Form

Added proof-independent endpoint data:

```text
universalPaymentBlockSignedDriftAt(n, j)
  = claim card - endpoint capacity
```

For every nonempty universal source fiber this is exactly the signed width
change from the universal block start to the state after the endpoint.

## Consequence

Universal payment blocks with no delayed growth debt are now included in the
same accounting theorem.  They can carry capacity surplus and therefore are
not removable from any later cumulative/telescoping argument.

## Validation

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
```

completed successfully.  No new `sorry` or `axiom` was introduced.
