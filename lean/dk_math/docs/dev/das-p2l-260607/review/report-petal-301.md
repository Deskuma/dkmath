# cp-301: Payment multiplicity and capacity

## Result

Added `DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge` and
exported it from `DkMath.Collatz.PetalBridge.FloatWindow`.

The module makes the delayed-payment geometry finite and explicit.  It does
not identify target coincidence with pressure or with an unpaid debt.

## Fixed facts

### 1. Pre-payment staircase

`orbitDepthRecoversExactlyAt_prePayment_chain` proves that an exact all-ones
depth `d >= 2` produces:

```text
for t < d - 1:
  exact depth at i + t is d - t
  observed height at i + t is exactly 1

at i + d - 1:
  observed height is at least 2
```

Thus the delayed endpoint is the first forced extra-height payment, rather
than merely an endpoint known to have enough height.

### 2. Canonical target

`floatDebtPaymentTarget n i` is defined as:

```text
i + ResidualAllOnesDepth (oddOrbitLabel n i) - 1
```

The old proof-carrying relation is now proved to be exactly the graph of this
target map:

```text
FloatDebtPaymentDischarge n i j
  <-> FloatDebtAt n i and j = floatDebtPaymentTarget n i
```

The relation is retained because it carries the exact-depth payment proof;
the deterministic target is used for finite fibers.

### 3. Collision versus overload

`floatGrowthDebtFiberAt n j` is the finite set of Float growth debts targeting
`j`.  It satisfies:

```text
FloatPaymentCollisionAt n j
  <-> 2 <= (floatGrowthDebtFiberAt n j).card
```

The actual capacity is:

```text
extraPaymentCapacityAt n j = orbitWindowHeight n j - 1
```

and the genuine overload predicate compares capacity with the fiber card.

```text
FloatPaymentOverloadAt n j -> FloatPaymentCollisionAt n j
```

The converse is intentionally absent.  Two debts sharing a target are not an
overload if that target carries at least two extra-height units.

### 4. Complete carry-two ledger

The ledger now includes both branches of every carry-two event:

```text
DelayedCarryTwoDebtAt:   carry two and height one
ImmediateCarryTwoDebtAt: carry two and height at least two
```

`CarryTwoPaymentClaim` gives delayed debts their canonical target and immediate
debts their own time.  Its finite target fiber, collision predicate, and
capacity-overload predicate are all explicit.  The complete overload also
forces a complete-claim collision.

### 5. Diagonal geometry

For ordered Float debts with a common payment target:

```text
A_i1 = A_i2 + (i2 - i1)
```

where `A_i = orbitExactDepth n i`.  More strongly,
`floatDebtAt_same_paymentTarget_staircase_to_later_source` shows that every
intermediate time is on the earlier source's exact-depth, height-one staircase.
The later debt is therefore a later point on that same descending diagonal.

## Honest stopping point

The requested Stage G bridge is not an index equality.  It must compare a
diagonal target fiber with a *localized horizontal* continuation/recovery
fiber.  The existing `SourcePressureMarginInt` counts over `List.range k`.
Those global entries can contain recovery sources unrelated to one target
fiber, and no existing theorem maps a diagonal fiber to such a restricted
horizontal source set.

Consequently, no theorem of either form below was claimed:

```text
target collision -> positive source pressure
payment overload -> positive source pressure
```

The next legitimate layer is a generic finite-source-set pressure API:

```text
retention / continuation / recovery over Finset source indices
localized margin = continuation card - recovery card
List.range k specialization = existing source pressure
```

Only after mapping a payment diagonal into one such source set can overload be
compared to local horizontal pressure without silently discarding unrelated
recoveries.

## Verification

Passed during this checkpoint:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

No `sorry` or `axiom` was introduced in the new FloatWindow module.
