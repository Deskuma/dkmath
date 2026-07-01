# Collatz Cause-Side Frequency Alias 112

## Purpose

Checkpoint 112 adds a thin cause-side frequency layer to
`DkMath.Collatz.PetalBridge`.

Checkpoint 109 introduced descriptive pressure-frequency predicates:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

Checkpoint 110 proved that the cause-side outruns count is the same count as
the descriptive pressure count:

```lean
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

Checkpoint 112 exposes that same frequency question under cause-side names.

## New Frequency Predicates

Source:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
```

Tail:

```lean
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

These predicates count:

```text
how often continuation outruns recovery over the depth range [r, r + len)
```

They do not introduce a new count.  They reuse:

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

## Dichotomy

The finite half dichotomy is available directly on the cause-side names:

```lean
sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
```

So the cause-side question can now be split as:

```text
outruns is at most half of the depth range
or
outruns is more than half of the depth range
```

This is intentionally division-free.  It stays in `Nat` inequalities through
`AtMostHalf` and `MoreThanHalf`.

## Bridge To Pressure Frequency

The cause-side aliases are theorem-equivalent to the descriptive pressure
frequency predicates:

```lean
sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
```

This lets future proofs choose their input language.

Mechanism-side hypothesis:

```text
ContinuationOutrunsRecovery occurs often.
```

Budget-side API:

```text
MoreThanHalf continuation pressure occurs often.
```

The checkpoint 112 bridge identifies these two readings at frequency level.

## Extra Count Comparison

Checkpoint 112 also records the count comparison forced by cause-side
more-than-half:

```lean
sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
```

These theorems use the checkpoint 111 cause-side partition:

```text
dominanceDepthCount + outrunsDepthCount = len
```

and the definition of `MoreThanHalf`:

```text
len < 2 * outrunsDepthCount
```

to conclude:

```text
dominanceDepthCount < outrunsDepthCount
```

This is a small but useful obstruction reading: if the failure side occupies
more than half the range, then it has already beaten the recovery-dominance
side as a finite depth count.

## Next Candidate

The next useful bridge is not another alias layer.  It should ask what a
pressure-heavy or outruns-heavy depth range forces on the original Collatz
height data.

Candidate route:

```text
cause-side frequency
  -> pressure frequency
  -> controlled/pressure count comparison
  -> source/tail mass imbalance
  -> possible height or drift lower bound
```

The current checkpoint prepares the language needed to state that route
without unfolding the count definitions.
