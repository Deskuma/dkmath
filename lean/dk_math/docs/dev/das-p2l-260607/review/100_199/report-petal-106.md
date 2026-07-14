# Report Petal 106: More-Than-Half Pressure

## Summary

Checkpoint 106 implements the comparison split requested by
`__next_implementation-106.md`.

The previous checkpoint introduced named comparison predicates such as:

```lean
RecoveryDominatesContinuation
ContinuationOutrunsRecovery
```

Checkpoint 106 turns them into a usable local dichotomy and gives the failure
branch a positive finite interpretation:

```text
if continuation outruns recovery,
then continuation is more than half of the parent retention mass.
```

This is still a finite `Nat` counting layer.  It does not use probability,
limits, or real-valued frequency.

## Lean Additions

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New finite strict-half predicate:

```lean
MoreThanHalf
atMostHalf_or_moreThanHalf
```

Local comparison dichotomy:

```lean
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
```

Failure excludes dominance:

```lean
not_recoveryDominates_of_continuationOutruns
not_tailRecoveryDominates_of_tailContinuationOutruns
```

Range extraction:

```lean
continuationOutrunsRecovery_of_onRange
tailContinuationOutrunsRecovery_of_onRange
```

Failure-pressure theorems:

```lean
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
moreThanHalf_continuation_of_outRunsOnRange
moreThanHalf_tailContinuation_of_outRunsOnRange
```

## Mathematical Result

The local Petal channel split is:

```text
retention = recovery + continuation
```

Checkpoint 104 proved the controlled branch:

```text
continuation <= recovery
  -> continuation is at most half of retention
```

Checkpoint 106 proves the obstruction branch:

```text
recovery < continuation
  -> continuation is more than half of retention
```

So every local depth now has a readable two-way interpretation:

```text
RecoveryDominatesContinuation
  -> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

This is the requested False/obstruction philosophy in a small formal form.  A
failure of the desired comparison is not thrown away; it becomes a measurable
pressure signal.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md
```

## Additional Inference

The useful next observation is not an immediate global Collatz contraction.
The proof surface now suggests a finite pressure-profile layer.

If the failure branch persists over a range:

```text
ContinuationOutrunsRecoveryOnRange n k r len
```

then each depth in the range carries strict more-than-half continuation
pressure.  This suggests the next API should package repeated pressure rather
than trying to prove the branch impossible too early.

Candidate next predicates:

```lean
def MoreThanHalfOnRange ...
def ContinuationPressureOnRange ...
```

Candidate next theorem shape:

```text
ContinuationOutrunsRecoveryOnRange
  -> MoreThanHalfOnRange continuation retention
```

or a count of pressure depths:

```text
number of depths j < len where continuation outruns recovery
```

This would turn prolonged obstruction into a finite object that can later be
compared with height drift, collision, or retention-cylinder depletion.

## Verification

Commands run for this checkpoint:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched files>
```

Results:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

Known upstream warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
```

This warning is outside the Collatz `PetalBridge` checkpoint.

## Next Implementation Candidate

Proceed to a pressure-profile checkpoint.

Recommended minimal surface:

```lean
def MoreThanHalfOnRange
    (count total : ℕ -> ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len -> MoreThanHalf (count (r + j)) (total (r + j))
```

Then add source/tail specializations using the existing range-to-pressure
theorems.  Keep it thin: package the repeated observation first, and postpone
any attempt to prove long failure ranges impossible.
