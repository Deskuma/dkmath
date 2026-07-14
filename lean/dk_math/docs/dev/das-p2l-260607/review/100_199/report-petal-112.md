# Report Petal 112

## Summary

Checkpoint 112 adds cause-side frequency aliases to
`DkMath.Collatz.PetalBridge`.

The previous checkpoints proved that:

```text
outrunsDepthCount = pressureDepthCount
dominanceDepthCount = controlledDepthCount
```

Checkpoint 112 uses the first equality to expose pressure-frequency predicates
under cause-side names.  No new count induction was needed.

## Lean Additions

New source cause-side frequency predicates:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
```

New tail cause-side frequency predicates:

```lean
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

Finite dichotomies:

```lean
sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
```

Pressure-frequency bridges:

```lean
sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
```

Extra cause-side count comparisons:

```lean
sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
```

## Mathematical Reading

Checkpoint 112 makes the frequency question readable on the mechanism side:

```text
How often does continuation outrun recovery?
```

The same question was already readable on the descriptive pressure side:

```text
How often is continuation more than half of retention?
```

The new bridge theorems identify these two frequency readings.

The extra count comparison records the finite obstruction:

```text
if outruns occurs in more than half of the depth range,
then outruns depths strictly outnumber recovery-dominance depths.
```

This follows from the cause-side partition:

```text
dominanceDepthCount + outrunsDepthCount = len
```

and the `MoreThanHalf` inequality.

## Documentation Updates

Updated:

```text
DkMath/Collatz/README.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

The no-sorry check returned no matches in `DkMath/Collatz/PetalBridge.lean`.

```text
Known upstream warning during the integration build:
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 uses sorry.
```

## Next Candidate

The next step should connect frequency to actual Collatz height or drift
information.

Suggested route:

```text
cause-side frequency
  -> pressure frequency
  -> controlled/pressure count comparison
  -> source/tail mass imbalance
  -> height or drift lower bound
```

The likely next small theorem is a named bridge from
`SourceOutrunsMoreThanHalfOnDepthRange` to the existing controlled/pressure
comparison theorem, then a search for where that comparison can feed a height
or shifted-tail mass estimate.
