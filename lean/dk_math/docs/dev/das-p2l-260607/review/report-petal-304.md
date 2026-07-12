# cp-304 Payment Block Ledger

## Result

The payment-block accounting branch is now closed without `sorry` or new
axioms in `PaymentBlockBridge.lean`.

The implementation avoids successor normalization of `Finset.Ico` during the
recursive proofs.  It first works over local offsets `t ∈ range len`, with
global time `a + t`, then transports that finite carrier to the canonical
global block.

## Proven finite transport

- `shiftedCarryTwoOffsets` represents carry-two sources in `[a, a + len)`.
- `shiftedOrbitCarryTwoCount_eq_offset_card` identifies the recursive count
  with the offset-set cardinality.
- `shiftedExtraPaymentCapacity_eq_sum_range` identifies the recursive
  capacity with the corresponding local finite sum.
- `shiftedCarryTwoPositions_eq_carryTwoPositions_Ico` proves that offset
  translation `t ↦ a + t` gives precisely the carry-two positions of the
  global half-open interval.
- `shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card` specializes
  this transport to a canonical block and its complete claim fiber.

## Endpoint concentration

`extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra`
proves that every non-endpoint term contributes zero: the block interior has
height one, so all extra-height capacity is concentrated at its endpoint.
Consequently,
`shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt` specializes the
shifted segment sum to `extraPaymentCapacityAt n j`.

## Exact block classification

For a nonempty growth-debt fiber at endpoint `j`, with canonical start `a`, the
new ledger is:

```text
bitWidth (iterateT (j + 1) n) + extraPaymentCapacityAt n j
  = bitWidth (iterateT a n) + card (carryTwoPaymentClaimFiberAt n j)
```

Lean now proves three exact equivalences:

```text
claim card > capacity  iff width strictly grows
claim card = capacity  iff width is preserved
claim card < capacity  iff width strictly decreases
```

These are local block-accounting facts only.  They do not assign individual
claims to individual capacity units, claim global interval coverage, or infer
an ambient pressure/convergence conclusion.

## Next work

The immediate target in the current branch is complete.  A later universal
payment-target layer may quantify this ledger over endpoint families, but it
needs new hypotheses that connect local canonical blocks; it should not be
inferred merely from the finite transport proven here.
