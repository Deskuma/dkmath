# report-petal-155

Checkpoint: 155

Subject: lift explicit local-island witness lists to pulse-address families.

## Summary

This checkpoint extended:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

No `PressureFrontier`, `OneCycle`, `ValuationFlowBridge`, ABC, or
NumberTheory files were modified.

The new layer accepts an explicit list of local-island witnesses and maps it
to the pulse-address family API introduced in checkpoints 153-154.

## Witness Carrier

Added:

```lean
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : Nat)
```

The implementation uses:

```lean
{ j : Nat // SourcePressureLocalIsland n k r j }
```

This is the Lean-safe form of the intended mathematical carrier:

```text
Sigma j, SourcePressureLocalIsland n k r j
```

The reason is that `SourcePressureLocalIsland n k r j` lives in `Prop`, so a
plain dependent sigma over it is not the right executable list carrier here.

## One-Witness Conversion

Added:

```lean
def sourcePressureIntervalPulseAddress_of_localIslandWitness
```

This uses the existing producer:

```lean
sourcePressureIntervalPulseAddress_of_localIsland
```

and converts one indexed local-island witness into one
`SourcePressureIntervalPulseAddress`.

## Witness List Conversion

Added:

```lean
def sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
```

It maps the explicitly supplied witness list into a
`SourcePressureIntervalPulseAddressFamily`.

Length wrapper:

```lean
theorem sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList_length
```

## Sorted / Failure Layer

Added:

```lean
def SourcePressureLocalIslandWitnessListSortedBefore
def SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
theorem sourcePressureLocalIslandWitnessList_sorted_or_failure
```

The sorted/failure split is inherited from the produced pulse-address family.

The failure side remains only sorted-before failure after conversion.  It does
not imply overlap and does not say the list is complete.

## Accounted-Family Lift

Added:

```lean
def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
```

and wrappers:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
```

These reuse the sorted pulse-address family budget API.  The cost statement is
still only over the explicitly supplied witness list.

## Singleton Convenience

Added:

```lean
def sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness_length
```

This is a small convenience wrapper for one indexed local-island witness.

## Non-Claims

This checkpoint does not enumerate all local islands.

This checkpoint does not introduce:

```text
maximality
uniqueness
coverage
prefix behavior
union accounting
Collatz convergence
```

All statements remain about explicitly supplied local-island witnesses.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

The `rg` checks returned no matches.

The build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
```

That warning is outside checkpoint 155.

## Next Inference

The next conservative step is to add small bridge facts for singleton local
island witnesses:

```text
one witness
  -> singleton family
  -> sorted branch is immediate
  -> accounted family has length 1 and net drop <= -1
```

This would stay within explicit witness accounting and still avoid any claim
that all local islands have been found.
