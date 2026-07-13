# Petal / Collatz implementation report: cp-316

## Result

Checkpoint cp-316 replaces the refuted depth-to-level repayment candidate with
the anonymous scalar repayment queue justified by the exact endpoint ledger.
The requested algebraic, queue-reflection, repayment, temporal Hall, matching,
and queue-to-bit-width surfaces are proved in Lean without `sorry`.

The checkpoint also reaches the requested genuine obstruction.  Uniform queue
boundedness is now proved equivalent to a uniform bound on every signed suffix
of the endpoint-accounting walk.  Existing local block data does not yet supply
that global suffix estimate.  Therefore this checkpoint does not promote the
finite observed queue ceiling to a theorem.

The new main module is:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
```

It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.

## Anonymous scalar ledger

The implementation freezes the semantic distinction identified at cp-315:

```text
recovery depth           = intrinsic address within a canonical block
endpoint capacity level  = coordinate on anonymous unit-capacity slots
```

Neither coordinate carries a proved exchange value.  The scalar layer therefore
counts only unit claims and fungible unit service:

```text
canonicalBlockClaimCount
canonicalBlockCapacityCount
```

Lean proves exactly:

```text
endpointAccountingTerm n k
  = canonicalBlockClaimCount n k - canonicalBlockCapacityCount n k
```

where the subtraction on the right is interpreted in `Int`.

## Reflected causal queue

`canonicalOutstandingClaimQueue` implements a work-conserving reflected queue.
New claims are added, current endpoint capacity is consumed, and unused capacity
is discarded rather than banked.

Lean proves two exact reflection forms.

First, the queue is the largest nonnegative signed suffix drift ending at block
`m`:

```text
queue n m
  = max (Int.toNat (canonicalWindowDriftInt n q m)), q <= m
```

The implementation is exposed by:

```text
canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum
```

Second, it is the current endpoint balance reflected above the running minimum:

```text
queue n m
  = Int.toNat
      (balance n m - runningMinimum n m)
```

This is proved by
`canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum`.

These are theorem-level identities, not numerical observations.

## Repayment characterization

Lean proves:

```text
queue n m = 0
  <-> every suffix q..m has nonpositive signed drift
  <-> every aggregate excursion ending at m is repaid
```

The corresponding public theorems are:

```text
canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos
canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
```

This distinguishes aggregate repayment from causal repayment.  One total
window inequality is not enough for causal service when claims have release
blocks.

## Temporal Hall theorem

For `q <= r`, Lean now proves the finite interval-order Hall theorem:

```text
CanonicalEndpointForwardWindowMatching n q r
  <-> forall t in q..r,
        claims n t r <= capacity n t r
```

The forward direction restricts an existing injection to each suffix.  The
reverse direction applies finite Hall to the anonymous claim and capacity
carriers; for an arbitrary nonempty claim subset, its minimum release block
reduces the Hall neighborhood bound to one nested suffix inequality.

No depth or capacity-level coordinate occurs in this theorem.

The local reflected queue is then proved equivalent to actual causal matching:

```text
canonicalLocalOutstandingClaimQueue n q r = 0
  <-> CanonicalEndpointForwardWindowMatching n q r
```

Thus the following three descriptions are now interchangeable:

```text
all suffix inequalities
local queue zero
anonymous forward matching
```

## Exact regressions

The existing explicit seven allocation is now packaged as the actual theorem:

```text
CanonicalEndpointForwardWindowMatching sevenDepthRegressionRoot 0 1
```

Lean also proves the scalar queue values:

```text
root 7:    queue 0 = 1, queue 1 = 0
root 511:  queue 0 = 5, queue 1 = 4, queue 2 = 0
```

For root 511 the proof first establishes the exact endpoint drifts
`+5, -1, -5` from accelerated states and bit widths, then derives the reflected
queue.  This is the intended contrast with cp-315: the exact-level candidate
leaves depth-eight and depth-nine claims, while the justified anonymous scalar
ledger is fully repaid after three blocks.

## Queue to Big

Lean proves that endpoint balance never exceeds the nonnegative reflected queue:

```text
canonicalEndpointBalanceInt n m
  <= canonicalOutstandingClaimQueue n m
```

Consequently:

```text
uniform scalar queue bound
  -> CanonicalEndpointBalanceUniformUpperBound
  -> canonical endpoint bit-width bound
```

This is the first direct scalar queue-to-Big bridge.  It remains conditional on
proving a uniform queue ceiling.

## Finite scalar audit

The new executable audit is:

```text
python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
```

It audits all `8192` odd roots in `1..16383`, independently of the rejected
level queues, and records block-local features at the first maximum queue.

Finite observations:

```text
roots audited                            8192
roots reaching a state-one endpoint     8192
nonzero queue at that endpoint              0
largest observed scalar queue               8
longest observed positive excursion        20 blocks
```

The 511 assertions are embedded in the script as executable regressions.  The
largest observed queue occurs for several roots, including `4255`, `4591`, and
`5673`.  The longest positive excursion occurs at root `7527`.

Generated evidence:

```text
python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.csv
python/Collatz/PetalBridge/results/canonical_scalar_queue_audit_316.md
```

These statements concern only the audited finite set.  They do not prove that
all roots reach state one, that queue eight is a universal ceiling, or that
twenty blocks is a universal repayment lag.

## Exact structural frontier

The additional cp-316 theorem makes the remaining target precise:

```text
canonicalOutstandingClaimQueue n m <= C
  <-> forall q <= m, canonicalWindowDriftInt n q m <= C
```

and uniformly:

```text
CanonicalOutstandingClaimQueueUniformUpperBound n C
  <-> forall m q, q <= m -> canonicalWindowDriftInt n q m <= C
```

This is the safe stopping point.  Reflection and temporal Hall completely
explain the queue, but neither bounds a positive queue.  The existing canonical
block length, claim-depth histogram, endpoint height, block-pressure, and
PatternLedger surfaces describe individual transitions; no current theorem
prevents arbitrarily long accumulation of positive suffix drift.

The next mathematical input must therefore establish at least one of:

```text
uniform signed-suffix control
uniform repayment lag
absence of a pumpable positive-queue cycle
finite-state obstruction forcing discharge
```

Returning to exact depth-to-level matching would not address this obstruction
without a new theorem assigning payment semantics to those coordinates.

## Verification

Completed during implementation:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
python3 python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
python3 -m py_compile python/Collatz/PetalBridge/canonical_scalar_queue_audit.py
git diff --check
```

All build gates passed.  The cp-316 Lean module contains no `sorry`.  Existing
unrelated project warnings remain outside this checkpoint.

