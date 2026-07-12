# Report: Universal Payment Blocks, cp-311

## Scope

This checkpoint continued `DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock` at finite, exact orbit accounting. No global convergence claim is made.

## Implemented facts

### A. Debt-free universal blocks

For a nonempty universal payment fiber at endpoint `j`, under `floatGrowthDebtFiberAt n j = empty`, Lean now proves:

- each strict interior source has `orbitWindowHeight = 1` and `stateUpperCarry = 1`;
- `i in carryTwoPaymentClaimFiberAt n j` iff `i = j` and `CarryTwoDebtAt n j`;
- the complete claim fiber is the endpoint singleton when that carry is two, and is empty otherwise;
- claim cardinality is at most one and at most endpoint capacity;
- signed block drift is nonpositive, so the block cannot increase bit width.

The key local contradiction is exact: an interior carry-two event plus the known height-one profile is a delayed debt for this same endpoint.

### B. Equality and strict decay

Under those same assumptions:

```text
universalPaymentBlockSignedDriftAt n j = 0
  iff CarryTwoDebtAt n j and orbitWindowHeight n j = 2
```

All other debt-free universal blocks have negative signed drift and strictly decrease bit width.

### D/E. Canonical endpoint blocks

Added `paymentEndpointSeq`, starting from the target of time zero and then taking the target immediately after each endpoint. Lean proves:

- successive entries are strictly increasing;
- every entry is an extra-height endpoint fixed by `orbitPaymentTarget`;
- every entry has a nonempty universal source fiber;
- the first block starts at zero;
- block `k + 1` starts at `paymentEndpointSeq n k + 1`.

The last result uses target monotonicity: an earlier source can target at most the old endpoint, but the next endpoint is strictly larger.

## Proven conclusion

Canonical target fibers now have consecutive block starts. Separately, every debt-free block is either width-preserving in its unique endpoint-carry-two/height-two equality case, or strictly width-decreasing. These are local conditional facts; they do not assert that every block is debt-free.

## Remaining frontier

1. Stage C: universal/debt-supported start compatibility and zero-drift prefix.
2. Stage F/G: endpoint-aligned finite partition and telescoping signed ledger.
3. Stage H: exact block-depth contribution formulas and pressure sums.

The start formulas added here remove the coordinate mismatch required by the finite telescope.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

No `sorry` or axioms were added.
