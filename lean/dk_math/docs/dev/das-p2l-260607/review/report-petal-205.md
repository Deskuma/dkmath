# report-petal-205

## Situation

Checkpoint `petal-205` asked whether a raw `SourcePressureBeamSeed L`
contains at least one explicit depth target.

The important boundary is:

```text
SourcePressureBeamSeed L
  -> exists contained witness depth
  -> exists Beam depth target
```

This is existential extraction from already supplied witness data.  It is not
arbitrary target transport.

## Lean Experiments

### T1: raw seed contains some explicit witness depth

Implemented:

```lean
theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamSeedContainsDepth L j
```

Result: passed.

The proof splits `SourcePressureFailureResolution` into recovered and overlap
branches.

### T2: raw seed gives some Beam depth target

Implemented:

```lean
theorem exists_sourcePressureBeamDepthTarget_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamDepthTarget n k r j
```

Result: passed.

This uses T1 plus `sourcePressureBeamDepthTarget_of_seedContainsDepth`.

### T3: paired contained-depth and target statement

Implemented:

```lean
theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamSeedContainsDepth L j ∧
        SourcePressureBeamDepthTarget n k r j
```

Result: passed.

This fixes the same existential depth on both the list-address side and target
side.

## Branch Analysis

Recovered branch:

```text
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
  -> SourcePressureBeamSeedContainsDepth L A.val
```

Implemented helper:

```lean
theorem sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left
```

The left witness of the addressed adjacent pair is enough to expose an exact
depth contained in `L`.

Overlap branch:

```text
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> exists contained depth
```

Implemented helper:

```lean
theorem exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
```

The obstruction predicate is recursive over adjacent list pairs, so the head
overlap branch exposes the first witness depth, and the tail branch lifts the
recursive witness back into the larger list.

## True Beam Facts

| theorem | status | meaning |
| --- | --- | --- |
| `sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left` | passed | an addressed recovered pair exposes the left witness depth |
| `exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction` | passed | an adjacent-overlap obstruction still exposes some listed depth |
| `exists_sourcePressureBeamSeedContainsDepth_of_seed` | passed | raw seed contains some explicit witness depth |
| `exists_sourcePressureBeamDepthTarget_of_seed` | passed | raw seed produces some Beam depth target |
| `exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed` | passed | same existential depth carries both containment and target facts |

## False Beam / Gap

The known Gap remains:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

for arbitrary `j`.

The implemented theorems do not try to prove this.  The data in a raw seed only
selects existential witness depths from `L`; it does not identify every external
depth as a target.

No new negated theorem was needed in this checkpoint.

## Guardrails Kept

No theorem was added for:

- arbitrary target transport;
- propagation over time or orbit;
- convergence;
- global coverage;
- arbitrary-list recursive decomposition;
- canonical first diagnosis;
- enumeration of all diagnostics;
- aggregation over multiple recovered diagnostics;
- interval union accounting;
- overlap repair;
- maximality;
- uniqueness;
- sorting;
- disjointness between multiple recovered families.

## One-Step-Ahead Inference

The next safe surface is an addressed existential target carrier, for example:

```text
SourcePressureBeamSeed L
  -> exists j, SourcePressureBeamSeedContainsDepth L j
               and SourcePressureBeamDepthTarget n k r j
```

This checkpoint already proves that theorem directly.  The next useful layer
should therefore avoid re-proving the same fact and instead decide whether a
named structure or predicate is worth adding around this paired existential.

A safe candidate would be a thin addressed carrier, not an aggregation layer:

```lean
def SourcePressureBeamAddressedDepthTarget
    (L : List (SourcePressureLocalIslandWitness n k r)) (j : ℕ) : Prop :=
  SourcePressureBeamSeedContainsDepth L j ∧
    SourcePressureBeamDepthTarget n k r j
```

That would be an API convenience only.  It should not claim coverage, canonical
selection, overlap repair, or list-wide accounting.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean ...
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry check over the requested pressure files: no matches.
- `git diff --check`: passed.

Known unrelated build warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

