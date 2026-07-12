# cp-308 Universal Claim and Capacity Accounting

## Result

The universal payment-block geometry is now connected to the complete
carry-two claim ledger without requiring a nonempty delayed Float-growth debt
fiber.

This is important because a universal block may have no delayed carry-two
source while still carrying endpoint capacity.  Such a block must remain in
the eventual cumulative ledger as a capacity-surplus / width-decay candidate.
The new theorems therefore use only the nonempty universal source fiber,
equivalently the fact that the endpoint is an extra-height time.

## Pure Fiber API

`mem_orbitPaymentSourceFiberAt_iff_target_eq` removes the finite-range clause
from the source-fiber interface:

```text
i belongs to the source fiber at j
iff
orbitPaymentTarget(i) = j
```

The omitted inequality is not an additional assumption.  It follows from the
extensivity theorem `i <= orbitPaymentTarget(i)`.

## Complete Claim Filter

For a nonempty universal fiber at `j`, with block start `b`, Lean proves:

```text
i belongs to carryTwoPaymentClaimFiberAt(j)
iff
i belongs to Icc(b, j) and CarryTwoDebtAt(i)
```

The proof has the two required semantic branches:

- for `i < j`, universal block geometry gives height one; a carry-two event is
  a delayed claim whose target is `j`;
- for `i = j`, the endpoint has height at least two; a carry-two event is an
  immediate self-claim.

Thus the complete claim fiber is exactly the `CarryTwoDebtAt` filter of the
entire universal block, not merely of the delayed-growth suffix.

## Capacity Concentration

The finite sum over the universal block is now fixed:

```text
extraPaymentCapacityOn(Icc(b, j)) = extraPaymentCapacityAt(j)
```

Every strict interior contribution is zero because every strict interior time
has height one.  The endpoint is the only possible positive extra-height
contribution.

## Consequence

The direct universal block ledger is now a transport step away:

```text
generic shifted width ledger at b over length (j + 1 - b)
  + universal claim-filter cardinality
  + universal endpoint-capacity concentration
```

No debt-supported assumption is needed for that target theorem.

## Validation

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
```

completed successfully.  The new theorems use no `sorry` or `axiom`.
