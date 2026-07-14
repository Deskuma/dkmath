# Collatz Finite Half Criterion 104

Checkpoint 104 adds the first finite half-criterion layer on top of the
source/tail retention splits.

The previous checkpoints established:

```text
source retention = source recovery + source continuation
tail retention   = tail recovery   + tail continuation
```

Checkpoint 104 does not prove that continuation always contracts.  Instead, it
formalizes the local comparison conditions that are sufficient to obtain an
`AtMostHalf` conclusion.

## Main Source Criterion

The source theorem is:

```lean
atMostHalf_continuation_of_continuation_le_recovery
```

It reads:

```text
source continuation <= source recovery
  -> source continuation is at most half of source retention
```

The proof uses:

```lean
orbitWindowRetentionMass_split
```

and then closes by finite `Nat` arithmetic.

## Main Tail Criterion

The shifted-tail theorem is:

```lean
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

It reads:

```text
tail continuation <= tail recovery
  -> tail continuation is at most half of tail retention
```

The proof uses:

```lean
orbitWindowRetentionMassPow2Tail_split
```

## Recovery-Budget Variants

There are also equivalent-looking budget forms:

```lean
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

These read:

```text
retention <= 2 * recovery
  -> continuation is at most half of retention
```

They are useful when a future argument naturally produces a lower bound on
recovery rather than a direct `continuation <= recovery` comparison.

## Ratio Witness Bridges

Checkpoint 104 also connects child-mass bounds to the division-free ratio
predicate:

```lean
continuation_atMostRatio_one_one_retention
tailContinuation_atMostRatio_one_one_retention
recovery_atMostRatio_one_one_retention
tailRecovery_atMostRatio_one_one_retention
```

These are weak `1/1` bounds, but they make the ratio layer consume the mass
split vocabulary rather than raw residue counts.

## Tail Budget Alias

The continuation destination budget also has a shorter alias:

```lean
orbitWindowContinuationMass_tailBudget
```

It restates:

```text
source continuation <= tail recovery + tail continuation
```

This is the finite mass-flow target that later obstruction or contraction
claims should refine.

## Next Candidate

The next real question is not arithmetic bookkeeping.  It is the source of a
comparison:

```text
continuation <= recovery
```

or:

```text
retention <= 2 * recovery
```

Possible future routes:

```text
height drift:
  continuation-heavy paths must pay extra height later

collision/obstruction:
  too much continuation creates repeated addresses or closed low-peeling loops

carrier structure:
  odd-factor or Petal carrier information forces recovery mass to appear
```

Checkpoint 104 isolates that missing comparison as the next mathematical
target.
