# Collatz More-Than-Half Pressure 106

## Purpose

Checkpoint 106 closes the local comparison split introduced at checkpoint 105.

Checkpoint 105 named the desirable comparison hypotheses:

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
```

Those predicates are still hypotheses.  They do not say that recovery always
dominates continuation.  Checkpoint 106 adds the complementary branch and gives
that branch a finite arithmetic meaning.

## New Predicate

The strict counterpart of `AtMostHalf` is:

```lean
def MoreThanHalf (count k : ℕ) : Prop :=
  k < 2 * count
```

The basic finite dichotomy is:

```lean
theorem atMostHalf_or_moreThanHalf
    (count k : ℕ) :
    AtMostHalf count k ∨ MoreThanHalf count k
```

This keeps the layer entirely in `Nat`.  No division, rational frequency, real
density, limit, or measure interpretation is required.

## Comparison Dichotomy

At each source depth:

```lean
theorem recoveryDominates_or_continuationOutruns
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ∨
      ContinuationOutrunsRecovery n k r
```

At each shifted-tail depth:

```lean
theorem tailRecoveryDominates_or_tailContinuationOutruns
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ∨
      TailContinuationOutrunsRecovery n k r
```

The reading is:

```text
either continuation is bounded by recovery,
or continuation strictly outruns recovery.
```

The outrunning branch also refutes the dominance branch:

```lean
not_recoveryDominates_of_continuationOutruns
not_tailRecoveryDominates_of_tailContinuationOutruns
```

These theorems are small, but they are useful for future case analyses.  They
prevent later proofs from repeatedly unfolding the same natural-number
comparison.

## Failure Becomes Pressure

The main checkpoint result is that failure is not merely a negative statement.
It becomes a positive pressure statement.

Source version:

```lean
theorem moreThanHalf_continuation_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r)
```

Tail version:

```lean
theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r)
```

The arithmetic proof uses the split:

```text
retention = recovery + continuation
```

and the strict comparison:

```text
recovery < continuation
```

Therefore:

```text
retention < 2 * continuation
```

This is the more-than-half pressure signature.

## Range Extraction

Checkpoint 106 also adds thin extraction theorems:

```lean
continuationOutrunsRecovery_of_onRange
tailContinuationOutrunsRecovery_of_onRange
```

and range-to-pressure theorems:

```lean
moreThanHalf_continuation_of_outRunsOnRange
moreThanHalf_tailContinuation_of_outRunsOnRange
```

Thus a finite range of failure hypotheses can be consumed one depth at a time
without unfolding the range predicate.

## Mathematical Reading

The local picture is now:

```text
RecoveryDominatesContinuation
  -> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

This is not a Collatz proof.  It is a verified observation law for the finite
Petal channel model.  It says that every local depth is forced into one of two
readable modes:

```text
controlled branch:
  continuation is at most half

obstruction branch:
  continuation is more than half
```

That is useful because an obstruction can now be accumulated, counted, or
compared against future drift and collision constraints.

## Next Candidate

The next useful layer is an accumulated pressure surface over a finite depth
range.

Possible targets:

```lean
def MoreThanHalfOnRange ...
def ContinuationPressureOnRange ...
```

or a counting theorem for the number of depths where:

```text
ContinuationOutrunsRecovery n k r
```

holds.

The point is not yet to prove that the failure branch is impossible.  The next
goal is to make prolonged failure visible as a finite, auditable pressure
profile.
