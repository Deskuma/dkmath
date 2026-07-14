# Collatz Comparison Predicates 105

Checkpoint 105 names the missing comparison conditions in the finite Collatz
Petal mass calculus.

Previous checkpoints established:

```text
M = R + K
K <= R -> AtMostHalf K M
M <= 2R -> AtMostHalf K M
```

What remains open is the structural source of either comparison:

```text
K <= R
```

or:

```text
M <= 2R
```

Checkpoint 105 does not prove those comparisons unconditionally.  It packages
them as explicit predicates so later arguments can state exactly which gap they
close.

## Local Comparison Predicates

Source comparison:

```lean
RecoveryDominatesContinuation
```

Tail comparison:

```lean
TailRecoveryDominatesContinuation
```

These read:

```text
continuation mass <= recovery mass
```

for the source or shifted-tail window.

## Budget Coverage Predicates

Source budget predicate:

```lean
RecoveryCoversHalfRetention
```

Tail budget predicate:

```lean
TailRecoveryCoversHalfRetention
```

These read:

```text
retention mass <= 2 * recovery mass
```

This form is useful when an argument produces a lower bound on recovery mass
rather than a direct comparison with continuation mass.

## Predicate-Facing Half Criteria

The source comparison predicate feeds:

```lean
atMostHalf_continuation_of_recoveryDominates
```

The tail comparison predicate feeds:

```lean
atMostHalf_tailContinuation_of_tailRecoveryDominates
```

The budget predicates feed:

```lean
atMostHalf_continuation_of_recoveryCoversHalf
atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
```

Thus later proofs can remain at the conceptual level:

```text
prove the comparison predicate
  -> obtain AtMostHalf
```

without unfolding the raw residue counts.

## Range Predicates

Persistent comparison over a finite depth range is named by:

```lean
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

These are deliberately thin:

```text
for all j < len, comparison holds at depth r+j
```

The point is not to prove persistence yet.  The point is to name the exact
hypothesis that an obstruction, drift, or carrier theorem must supply.

The current extraction theorems are:

```lean
atMostHalf_continuation_of_recoveryDominatesOnRange
atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
```

They give the corresponding half criterion at each depth in the finite range.

## Failure-Mode Predicates

The obstruction-facing side is named as well:

```lean
ContinuationOutrunsRecovery
TailContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
TailContinuationOutrunsRecoveryOnRange
```

These predicates record the opposite observation:

```text
recovery < continuation
```

They do not prove a contradiction.  They give the future obstruction route a
precise input shape.

## Next Mathematical Target

The next step is to find a source for the comparison predicate.

Candidate routes:

```text
height drift:
  continuation-heavy paths force extra 2-adic height later

collision / obstruction:
  persistent continuation creates repeated addresses or closed low-peeling loops

odd factor carrier:
  an additional arithmetic carrier forces recovery mass to appear
```

Checkpoint 105 isolates the missing theorem shape.  This is the formal gap:

```text
structural observation -> RecoveryDominatesContinuation
```

or, in budget form:

```text
structural observation -> RecoveryCoversHalfRetention
```

The corresponding obstruction target is:

```text
ContinuationOutrunsRecoveryOnRange
  -> height drift / address collision / finite budget pressure
```
