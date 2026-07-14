# Collatz Pressure Profile 107

## Purpose

Checkpoint 106 converted a failed local comparison into a positive observation:

```text
ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

Checkpoint 107 packages this observation over a finite depth range.

The goal is to move from:

```text
one depth has pressure
```

to:

```text
a finite range has a pressure profile
```

and then to start counting pressure depths.

## Generic Range Predicate

The generic pressure profile is:

```lean
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
```

This is deliberately independent of Collatz.  It only says that a pair of
depth-indexed finite counts satisfies `MoreThanHalf` at every depth in
`[r, r + len)`.

## Source And Tail Profiles

Source continuation pressure:

```lean
def SourceContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
    (fun d => orbitWindowRetentionMassPow2 n k d)
    r len
```

Tail continuation pressure:

```lean
def TailContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
    (fun d => orbitWindowRetentionMassPow2Tail n k d)
    r len
```

These predicates say that continuation carries strict more-than-half pressure
against the relevant retention mass at every selected depth.

## From Failure Range To Pressure Range

The failure range predicates now promote directly to pressure profiles:

```lean
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
```

The reading is:

```text
continuation outruns recovery at every depth
  -> continuation is more than half of retention at every depth
```

This makes the obstruction range reusable without unfolding the local
retention split theorem each time.

## Extraction

The profile can be consumed one depth at a time:

```lean
moreThanHalf_of_sourceContinuationPressure
moreThanHalf_of_tailContinuationPressure
```

These are intentionally thin aliases.  Their job is to keep later proofs
readable when a range hypothesis has already been established.

## Depth-Mode Count

Checkpoint 107 also introduces pressure depth counts:

```lean
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

These do not count points in the orbit window.  They count depths in a depth
interval:

```text
how many j < len are pressure depths?
```

This is a new finite distribution layer:

```text
window residue distribution
  counts labels inside a fixed depth

depth-mode distribution
  counts pressure/control modes across depths
```

The first count theorems are the all-pressure cases:

```lean
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

They say:

```text
pressure at every depth in the range
  -> pressure depth count = len
```

## Mathematical Reading

The current finite observation chain is:

```text
ContinuationOutrunsRecoveryOnRange
  -> SourceContinuationPressureOnRange
  -> pressure depth count = len
```

and similarly for the shifted-tail window.

This still does not prove that long pressure ranges are impossible.  Instead,
it names the object that a future obstruction theorem should attack:

```text
a prolonged pressure profile
```

## Next Candidate

The next natural checkpoint is a mixed depth-mode distribution.

Each depth already has a dichotomy:

```text
RecoveryDominatesContinuation
or
ContinuationOutrunsRecovery
```

Therefore a range should eventually split into:

```text
controlled depth count
pressure depth count
```

with a theorem of the shape:

```text
controlledCount + pressureCount = len
```

This would mirror checkpoint 100, but one level higher:

```text
checkpoint 100:
  finite window mass distribution

next route:
  finite depth-mode distribution
```
