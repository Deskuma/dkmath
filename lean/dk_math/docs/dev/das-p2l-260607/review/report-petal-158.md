# Report Petal 158

## Checkpoint

Checkpoint 158 focused on the main Collatz/Petal root:

- module: `DkMath.Collatz.PetalBridge.PressureAccounting`
- theme: failure-facing pair API for explicit local-island witnesses

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Implemented Theorems

The following witness-pair API was added.

```lean
theorem sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
    {n : OddNat} {k r : Nat}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
```

This is the direct failure-facing constructor.  It packages the negation of
the supplied before relation into the existing list-level sorted-before
failure predicate.

```lean
theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
    {n : OddNat} {k r : Nat}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
```

This records the positive side: if the first explicit local-island witness is
before the second, the two-witness list has no sorted-before failure.

```lean
theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) :
    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
```

This is a convenient two-witness split.  It specializes the existing
list-level sorted-or-failure theorem to an explicitly supplied pair.

## Raw Wrappers

The raw local-island wrappers were also added.

```lean
theorem sourcePressureLocalIsland_pair_hasSortedBeforeFailure_of_not_before
    (n : OddNat) (k r j1 j2 : Nat)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hfail :
      ¬ SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)]
```

```lean
theorem sourcePressureLocalIsland_pair_no_failure_of_before
    (n : OddNat) (k r j1 j2 : Nat)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hbefore :
      SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)]
```

These wrappers are intentionally verbose.  They keep the caller on the raw
`SourcePressureLocalIsland` surface while still using the explicit witness API
internally.

## Boundary Notes

The failure theorem is only an order-obstruction theorem.

It does not conclude interval overlap.  A pair may fail sorted-before because
the order is reversed.  Any future overlap theorem must add and prove the
extra hypotheses needed to distinguish reversal from genuine overlap.

This checkpoint also does not enumerate all local islands.  Every theorem is
about the explicitly supplied witnesses.

It does not introduce:

- maximality,
- uniqueness of pressure families,
- coverage,
- prefix behavior,
- union accounting,
- Collatz convergence.

## Verification

The following verification commands were run.

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

All three builds passed.

The target no-sorry checks were run:

```bash
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Both returned no hits.

`git diff --check` passed.

## Next Inference

The pair API is now symmetric enough for downstream callers:

- a sorted pair can be converted into an accounted interval family,
- a non-sorted pair can be reported as sorted-before failure,
- raw local-island facts can enter either branch without manually constructing
  witness values at the call site.

The next natural step is not to claim overlap.  The safer next branch is to add
an explicit predicate for overlap only after the interval-address layer exposes
the exact hypotheses needed to prove it.
