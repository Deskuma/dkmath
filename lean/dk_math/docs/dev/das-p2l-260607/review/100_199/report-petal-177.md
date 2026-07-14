# Report Petal 177

## Scope

Checkpoint 177 focused on the refactored Collatz/PetalBridge pressure modules.

Primary file:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Supporting file:

```text
DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
```

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Implemented Theorems

### Witness-address length positivity

Added:

```lean
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len
```

This is a witness-facing wrapper around:

```lean
SourcePressureIntervalPulseAddress.len_pos
```

The theorem is local to the supplied explicit witness.  It does not assert that
the witness belongs to a complete or canonical list of local islands.

### Explicit positivity theorem

Added:

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hpos :
      ∀ W ∈ L,
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

Proof strategy:

```text
structural induction on the explicit list L
nil: impossible by nil-failure false theorem
singleton: impossible by singleton-failure false theorem
cons-cons:
  use the existing one-step diagnosis
  head branch -> list-level diagnosis by `of_head`
  tail branch -> induction hypothesis, then lift by `of_tail`
```

### Clean public theorem

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

This discharges the positivity hypothesis using
`sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos`.

## Meaning

The new theorem says:

```text
If an explicitly supplied local-island witness list has sorted-before failure,
then some adjacent pair in that same explicit list carries an adjacent
diagnosis.
```

This moves the fixed length-three/four/five wrappers into the role of bounded
observational examples of the now-general explicit-list theorem.

## Non-Claims

The theorem does not assert:

```text
global local-island coverage
maximality
uniqueness
prefix behavior
arbitrary list sorting
canonical first diagnosis
enumeration of all diagnoses
union accounting
overlap repair
Collatz convergence
```

Recovered budgets remain pair-local.
Overlap remains an adjacent obstruction on the enclosing explicit list.

## Verification

Passed:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No-sorry check:

```bash
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no hits.

Known unrelated build warning still appears:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Candidate

The next natural step is to add small consumer-facing corollaries that project
the general adjacent diagnosis into either:

```text
some pair-local recovered budget
or
the enclosing list has an adjacent overlap obstruction
```

The existing projection theorem
`SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
already provides this once the new general theorem has produced the list-level
diagnosis.
