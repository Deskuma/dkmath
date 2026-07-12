# cp-302: Canonical payment blocks

## Result

Added `DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge` and exported
it through `DkMath.Collatz.PetalBridge.FloatWindow`.

The module corrects the semantic reading of the old `PaymentDischarge` name:
it provides a proof of a canonical first-payment claim and target, not a final
capacity allocation for every source in a colliding fiber.

## Established block geometry

For a nonempty delayed-growth target fiber at endpoint `j`, the canonical block
start is its least source index:

```text
a = min (floatGrowthDebtFiberAt n j)
```

The canonical block is split into:

```text
interior: [a, j)   -- exact height one
endpoint: j        -- height at least two
full block: [a, j]
```

The following are now formal facts.

- Every interior time has `orbitWindowHeight = 1`.
- The endpoint has `orbitWindowHeight >= 2`.
- Every interior time has first-payment target `j`.
- Every delayed Float debt targeting `j` lies in the interior.
- The delayed debt fiber is exactly the carry-two filter of the interior.
- The complete carry-two claim fiber at `j` is exactly the carry-two filter of
  the full block, including a carry-two endpoint precisely as an immediate
  self-claim.

Thus the block includes every intervening height-one state, including
carry-one states.  It is not merely the set of already-selected debts.

## Shifted ledger

Added the iterate transport theorem:

```text
iterateT (a + len) n = iterateT len (iterateT a n)
```

and the exact segment ledger:

```text
width(a + len) + shiftedExtraPaymentCapacity(a, len)
  = width(a) + shiftedOrbitCarryTwoCount(a, len)
```

This is obtained by applying the established prefix ledger to `iterateT a n`;
no duplicate induction over a segment was introduced.

## Remaining boundary

The intended endpoint-only payment-block identity still needs two explicit
reindexing theorems:

```text
shifted carry-two count on [a, j + 1)
  = card of the full canonical claim fiber

shifted extra-height sum on [a, j + 1)
  = extraPaymentCapacityAt j
```

The second equality uses the block fact that all interior heights are one.
The first equality transports the recursive count, based at `iterateT a n`,
to global interval coordinates.  Neither transport should be hidden in a
rewrite; they are reusable finite-orbit reindexing lemmas and deserve a small
separate API.

No theorem claiming `overload <-> block width growth` is made until both
identities are proven.  In particular, no first-payment claim is treated as a
final allocation.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

No `sorry` or `axiom` was introduced in `PaymentBlockBridge.lean`.
