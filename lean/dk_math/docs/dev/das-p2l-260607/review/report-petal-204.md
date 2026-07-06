# report-petal-204

## Situation Analysis

`petal-204` fills the previous Gap:

```text
seed list L --?--> target depth j
```

The goal was not to prove Beam propagation.  The goal was to ask Lean for the
smallest explicit relation connecting a supplied witness list to a target
depth.

The result is an exact-depth containment relation:

```lean
SourcePressureBeamSeedContainsDepth L j
```

This relation says that the supplied list contains a local-island witness whose
stored depth is exactly `j`.

## Actual Field Names Discovered

`SourcePressureLocalIslandWitness` is not a structure with named fields.  It is
a subtype abbreviation:

```lean
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : ℕ) :=
  { j : ℕ // SourcePressureLocalIsland n k r j }
```

Therefore the actual usable fields are the standard subtype projections:

- witness depth: `W.val`
- local-island proof: `W.property`

The local-island proof has the shape:

```lean
SourcePressureLocalIsland n k r W.val
```

and since

```lean
SourcePressureLocalIsland n k r j
  := 0 < j ∧
     IsSourcePressureDepth n k r j ∧
     ¬ IsSourcePressureDepth n k r (j - 1) ∧
     ¬ IsSourcePressureDepth n k r (j + 1)
```

the target-depth positivity part is available as:

```lean
W.property.2.1
```

with type:

```lean
IsSourcePressureDepth n k r W.val
```

## Added Relation

Added:

```lean
def SourcePressureBeamSeedContainsDepth
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  ∃ W ∈ L, W.val = j
```

This is the weakest exact-depth relation found in the current Core.  It does
not say that the list is a seed, complete, sorted, maximal, or covering.

## True Beam Facts That Passed

Added:

```lean
theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
    SourcePressureBeamDepthTarget n k r j
```

Result: passed.

Lean accepted this because exact-depth containment gives a witness `W` with
`W.val = j`, and `W.property.2.1` proves that the witness depth is a selected
source pressure depth.

## False Beam / Gap Observations

### Gap: raw seed still does not imply arbitrary target

The overbroad statement remains under-specified:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

Reason: a seed state alone says that the list has a failure-resolution state.
It does not say that the list contains a witness at the particular target
depth `j`.

This was not committed as a theorem.

### Gap converted to Core: exact-depth list containment

The previous missing relation is now partly filled:

```text
L contains a witness W with W.val = j
  -> depth target at j
```

This is a True Beam fact, but it is still local and explicit.

## Was a Seed-to-Target Theorem Added?

Yes, but only in the exact-containment sense:

```text
SourcePressureBeamSeedContainsDepth L j
  -> SourcePressureBeamDepthTarget n k r j
```

No theorem was added from `SourcePressureBeamSeed L` alone to a target depth.

## One-Step-Ahead Wise Wolf Inference

The next split is now visible:

```text
seed state
  versus
seed list address
```

`SourcePressureBeamSeed L` is an automaton/failure-resolution state.  It does
not by itself choose a target depth.

`SourcePressureBeamSeedContainsDepth L j` is a list-address relation.  It does
choose a target depth, but only because a witness at that exact depth is
already present in the list.

The next safe experiment is to connect the two without overclaiming:

```lean
theorem sourcePressureBeamDepthTarget_of_seed_and_containsDepth
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_hseed : SourcePressureBeamSeed L)
    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
    SourcePressureBeamDepthTarget n k r j
```

This theorem would intentionally ignore `_hseed`: its value is documentation
and API shape.  It states that a seed plus an explicit address relation gives a
target, while preventing future agents from pretending that seed alone is
enough.

Whether to add that wrapper should be decided in the next checkpoint.

## Experimental Lemma Table

| Experiment | Statement | Result |
| --- | --- | --- |
| Field inspection | witness depth is accessible as `W.val` | passed |
| Field inspection | witness proof is accessible as `W.property` | passed |
| R1 | define exact-depth list containment | passed |
| T1 | containment implies Beam depth target | passed |
| F1 | raw seed implies arbitrary target | under-specified / not committed |

## Guardrails Confirmed

This checkpoint did not add:

- a real propagation theorem;
- a convergence theorem;
- global coverage;
- arbitrary-list recursive decomposition;
- canonical first diagnosis;
- enumeration of all diagnostics;
- aggregation over multiple recovered diagnostics;
- interval union accounting;
- overlap repair;
- maximality;
- uniqueness;
- sorting theorem;
- disjointness between multiple recovered families.

The added theorem is local to an explicitly supplied list membership witness.

## Verification

Executed commands:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureBeam.lean \
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  DkMath/Collatz/PetalBridge/PressureDecay.lean \
  DkMath/Collatz/PetalBridge/DriftBudget.lean
git diff --check
```

Result:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry check over the pressure files listed above: no matches.
- `git diff --check`: passed.

The builds still replay the known unrelated warning in
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` about an existing
`sorry`.  This checkpoint did not touch that file.
