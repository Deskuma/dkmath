# report-petal-203

## Situation Analysis

`petal-203` is the first small Lean experiment checkpoint for the Beam layer.

The current Beam Core before this checkpoint was:

```lean
SourcePressureBeamSeed
sourcePressureBeamSeed_of_sortedBeforeFailure
sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
SourcePressureBeamDepthTarget
sourcePressureBeamDepthTarget_iff_margin_pos
```

The Beam layer is still intentionally local.  It names a seed state and a
depth target, but it does not transport a seed to a target.

## Review of What Was Tried

### Experiment T1

Tried and kept:

```lean
theorem sourcePressureBeamDepthTarget_of_margin_pos
    (n : OddNat) (k r j : ℕ)
    (h : 0 < SourcePressureMarginInt n k (r + j)) :
    SourcePressureBeamDepthTarget n k r j
```

Result: passed.

This is the constructor side of
`sourcePressureBeamDepthTarget_iff_margin_pos`.

### Experiment T2

Tried and kept:

```lean
theorem sourcePressureMargin_pos_of_beamDepthTarget
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureBeamDepthTarget n k r j) :
    0 < SourcePressureMarginInt n k (r + j)
```

Result: passed.

This is the projection side of
`sourcePressureBeamDepthTarget_iff_margin_pos`.

### Experiment G1

Overclaim considered:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

Result: Gap / under-specified.

Reason: `SourcePressureBeamSeed L` is a predicate on an explicit witness list
`L`, while `SourcePressureBeamDepthTarget n k r j` is a predicate at a single
relative depth `j`.  The current hypotheses do not relate the list `L` to the
target depth `j`.

This is not recorded as a False Beam theorem, because the statement may become
true after adding the missing relation.  It is a missing-structure problem.

### Experiment G2

Candidate missing relation:

```lean
SourcePressureBeamSeedTargetsDepth L n k r j
```

Result: report-only.

The fields are not yet obvious enough to implement.  A relation of this kind
must specify how a seed witness list points at, contains, reaches, or justifies
the target depth.  Those alternatives are different claims, and choosing one
too early would hard-code a transport interpretation.

## True Beam / False Beam / Gap

### True Beam

The following facts are now part of the Beam Core:

```lean
sourcePressureBeamDepthTarget_iff_margin_pos
sourcePressureBeamDepthTarget_of_margin_pos
sourcePressureMargin_pos_of_beamDepthTarget
```

Together they form the first complete local target API:

```text
Target iff margin_pos
Target of margin_pos
margin_pos of Target
```

### False Beam

No new negated theorem was added.

The main overclaim was not proved and not committed, but it is better recorded
as Gap rather than False Beam because it lacks a required relation instead of
contradicting current Core.

### Gap

Missing relation:

```text
seed list L  --?-->  target depth j
```

Without this relation, a theorem from `SourcePressureBeamSeed L` to
`SourcePressureBeamDepthTarget n k r j` is under-specified.

## Next Codex Instruction

Do not attempt a direct seed-to-depth transport theorem yet.

Next, design the minimal explicit relation between a Beam seed and a depth
target.  The first relation should be a predicate, not a theorem.  It should
avoid coverage, aggregation, uniqueness, maximality, and overlap repair.

Possible names:

```lean
SourcePressureBeamSeedTargetsDepth
SourcePressureBeamSeedContainsDepth
SourcePressureBeamSeedSupportsDepth
```

Recommended direction: use `TargetsDepth` only if the relation is intended to
be directional.  Use `ContainsDepth` only if the target depth is literally
extracted from a witness or interval address.

## One-Step-Ahead Inference from Wise Wolf

The next useful distinction is:

```text
list-address relation
  versus
depth-target relation
```

The Beam seed currently carries a list of local-island witnesses.  Each witness
has a value `j` and can be converted to an interval-pulse address.  Therefore
there are at least two possible target relations:

```text
1. target depth is the witness value itself
2. target depth lies inside the interval-pulse address produced by a witness
```

The second is stronger and closer to propagation/accounting, but it also risks
introducing interval membership and union reasoning too early.  The safer next
experiment is the first one: name a relation saying that a depth is one of the
explicit witness depths in the seed list.

## Experimental Lemmas Requested by Wise Wolf

| Experiment | Statement | Result |
| --- | --- | --- |
| T1 | margin positivity constructs a Beam depth target | passed |
| T2 | Beam depth target projects margin positivity | passed |
| G1 | arbitrary seed implies arbitrary target depth | under-specified |
| G2 | minimal seed-to-depth relation | report-only |

## Guardrails Confirmed

This checkpoint did not add:

- a propagation theorem;
- a convergence theorem;
- global coverage;
- aggregation over multiple recovered diagnostics;
- interval union accounting;
- overlap repair;
- arbitrary-list recursive decomposition;
- canonical first diagnosis;
- enumeration of all diagnostics;
- maximality;
- uniqueness;
- sorting theorem;
- disjointness between multiple recovered families.

The added theorems are local True Beam API wrappers around the existing target
equivalence only.

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
