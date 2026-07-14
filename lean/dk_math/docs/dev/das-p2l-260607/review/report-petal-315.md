# Petal / Collatz implementation report: cp-315

## Result

Checkpoint cp-315 closes the exact finite accounting and carrier-reindexing
work requested after cp-314, then reaches a genuine semantic obstruction.

Lean now proves exact excursion, window repayment, depth-ledger, carrier
equivalence, and seven-regression theorems.  A separate executable audit then
refutes the proposed exact-level eligibility rule on three of the four required
roots.  In each failing case exact integer evaluation reaches fixed state `1`
while a higher-level claim remains.  Consequently no general
`CanonicalRepaymentEligible` relation was exported.

This is the intended safe stopping condition: the rejected rule is represented
as an observable queue, not promoted into a false repayment API.

## Exact excursion and window repayment

The new module is
`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger`.

Lean proves:

```text
CanonicalEndpointPositiveExcursionAt n q
  <-> 0 < endpointAccountingTerm n q
```

For `q <= r`, Lean also proves that repayment from `q` through `r` is
equivalent to both:

```text
sum (endpointAccountingTerm n k), k in q..r <= 0
```

and

```text
window claims q..r <= window capacity q..r.
```

The proof uses the sliding endpoint-balance telescope.  It does not reuse the
weaker prefix-to-future-horizon embedding as a balance certificate.

Actual window claim and capacity carriers were added.  Their `Nat.card` values
are exactly the corresponding window totals.  The new
`CanonicalEndpointForwardWindowMatching` is an injective within-window map
whose payment block is not earlier than its claim block.  Lean proves that any
such matching repays the selected excursion.

## Scalar depth ledger

`canonicalEndpointCapacityLevelSlots` is the semantic alias for endpoint
capacity coordinates.  The signed term
`canonicalDepthAccountingTerm n k d` records claim incidence minus capacity
incidence at one numeric coordinate.

For every canonical block, Lean proves:

```text
endpointAccountingTerm n k
  = sum d in canonicalDepthAccountingSupport n k,
      canonicalDepthAccountingTerm n k d.
```

The family theorem then sums this exact block-local decomposition over all
blocks through `m`.  Thus the signed endpoint ledger is exposed level by level
without asserting that equal numeric levels are valid payment partners.

## Proof-independent carriers

The following carriers were added:

```text
CanonicalEndpointDepthClaimCarrier n m
CanonicalEndpointLevelCapacityCarrier n m
```

Their cardinalities are exactly cumulative claims and cumulative capacity.
More strongly, Lean constructs actual equivalences:

```text
CanonicalEndpointClaimCarrier n m
  ~= CanonicalEndpointDepthClaimCarrier n m

CanonicalEndpointCapacityCarrier n m
  ~= CanonicalEndpointLevelCapacityCarrier n m
```

The claim equivalence uses the injective exact recovery-depth coordinate.  The
capacity equivalence is the coordinate translation `slot s <-> level s + 2`.

## Exact seven regression

Lean proves the required finite sets:

```text
block 0 claims    = {2, 3}
block 0 capacity  = {2}
block 1 claims    = {1}
block 1 capacity  = {2, 3}
```

It also verifies the explicit forward allocation:

```text
(block 0, depth 2) -> (block 0, level 2)
(block 0, depth 3) -> (block 1, level 3)
(block 1, depth 1) -> (block 1, level 2)
```

The allocation has three distinct claims and three distinct capacity slots.

## Eligibility audit

The audit implementation is:

```text
python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
```

It mirrors the Lean definitions and asserts the exact seven regression before
running.  It tests claims from the first 1024 canonical blocks against capacity
through block 4095, and separately observes the streaming queue over all 4096
blocks.

The audited candidate was:

```text
depth 1 -> level 2
depth 2 -> level 2
depth d, d >= 3 -> level d
payment block >= claim block
```

Results:

| root | first state-1 time | prefix claims | outstanding | persistent detail | max lag |
| --- | ---: | ---: | ---: | --- | ---: |
| 7 | 5 | 1025 | 0 | none | 1 |
| 27 | 41 | 1032 | 1 | block 9, depth 5 -> level 5 | 14 |
| 31 | 39 | 1032 | 1 | block 8, depth 5 -> level 5 | 14 |
| 511 | 20 | 1027 | 2 | block 0, depths 8 and 9 -> levels 8 and 9 | 2 |

Roots 27 and 31 each also exhibit one simultaneous depth-1/depth-2 collision at
an endpoint with only one level-2 slot.  The queue can delay one of these
claims, so this collision alone is not the decisive counterexample.  The
decisive obstruction is a high-depth claim whose required exact level cannot
reappear after the simulation reaches state `1`: the accelerated step fixes
`1`, and its endpoint height is two.  This is an exact finite computation
followed by a fixed-point observation, but it is not promoted here to a Lean
theorem about these concrete roots.

Generated evidence is recorded in:

```text
python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.csv
python/Collatz/PetalBridge/results/canonical_depth_eligibility_audit_315.md
```

These files are finite computational evidence, not Lean proofs of an infinite
orbit statement.

## Corrected frontier

The rejected rule is retained only through:

```text
canonicalCandidateRequiredLevel
canonicalCandidateLevelDemand
canonicalCandidateLevelCapacity
canonicalCandidateLevelOutstandingQueue
CanonicalCandidateLevelQueuesUniformlyBounded
```

This makes the obstruction measurable and gives a comparison surface for a
future corrected rule.  The next rule must justify cross-level payment, or it
must derive a different capacity coordinate from the orbit.  Equal numeric
depth and level cannot be required globally.

The valid strong target remains a uniform canonical endpoint balance bound.
It implies a canonical endpoint bit-width bound by an existing theorem.  An
all-time bit-width bound still additionally needs a uniform in-block overshoot
bound, and eventual periodicity remains a separate finite-state implication.
No convergence or cycle-rigidity claim is made here.

## Verification

Completed during implementation:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
python3 python/Collatz/PetalBridge/canonical_depth_eligibility_audit.py
git diff --check
```

All build gates passed.  The new Lean module contains no `sorry`.  Existing
unrelated project warnings remain outside this checkpoint.
