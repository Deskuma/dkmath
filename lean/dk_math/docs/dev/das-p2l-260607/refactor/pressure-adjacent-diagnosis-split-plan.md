# Pressure Adjacent Diagnosis Split Plan

## Current State

`DkMath/Collatz/PetalBridge/PressureAccounting.lean` currently has about 3773
lines.

The adjacent-diagnosis declarations have become a coherent cluster.  They now
cover:

- pair-local recovered budget evidence;
- enclosing-list adjacent-overlap obstruction evidence;
- ordered adjacent-pair addresses inside explicit witness lists;
- list-level adjacent diagnosis carriers;
- bounded three-, four-, and five-witness wrappers.

This cluster is still local to explicitly supplied witness lists.  It does not
claim coverage, maximality, uniqueness, prefix behavior, union accounting, or
Collatz convergence.

The declarations are currently concentrated around `PressureAccounting.lean`
lines 3163-3674.  That makes them a plausible future extraction target, but the
dependencies below should be checked before any declaration movement.

## Candidate Cluster

### Adjacent Diagnosis Carrier

Candidate declarations:

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`

Role:

This is the pair-local/enclosing-list carrier.  The recovered branch remains
attached to the adjacent pair `A, B`; the overlap branch remains an obstruction
on the enclosing list `L`.

### Adjacent Pair Address Predicate

Candidate declarations:

- `SourcePressureLocalIslandWitnessAdjacentPairInList`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.head`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.tail`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false`

Role:

This is the ordered address layer for neighboring pairs only.  It is not
arbitrary pair membership and does not sort or classify a list.

### List-Level Adjacent Diagnosis Carrier

Candidate declarations:

- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false`

Role:

This is the public carrier for "some adjacent pair in this explicit list has a
diagnosis".  The carrier hides which adjacent pair was selected while still
preserving pair-local recovered evidence through projections.

### Bounded Diagnosis Wrappers

Candidate declarations:

- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier`
- `sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier`
- `sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis`
- `sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis`
- `sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis`

Role:

These are bounded wrappers for explicit lists of length three, four, and five.
They are observation tools, not a recursive algorithm.

### Projection And Propagation Helpers

Candidate declarations:

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`

Role:

These declarations make the bounded carrier usable by downstream files without
opening the full nested branch structure.

## Upstream Dependencies

### Carrier And Constructor Dependencies

Major dependencies:

- `SourcePressureLocalIslandWitness`
- `SourcePressureLocalIslandWitnessBefore`
- `SourcePressureIntervalNetDrop`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`
- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`

These must remain available before extracting
`SourcePressureLocalIslandWitnessAdjacentDiagnosis`.

### Address Predicate Dependencies

Major dependencies:

- `SourcePressureLocalIslandWitness`
- Lean `List`

This group is low-risk to extract once the witness carrier is available.  It
does not depend on pressure budgets or overlap obstruction.

### List-Level Carrier Dependencies

Major dependencies:

- `SourcePressureLocalIslandWitness`
- `SourcePressureLocalIslandWitnessAdjacentPairInList`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessBefore`
- `SourcePressureIntervalNetDrop`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure`
- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`

This group should be extracted only after the adjacent-pair address predicate
and adjacent-diagnosis carrier are available.

### Bounded Wrapper Dependencies

Major dependencies:

- `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis`
- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis`
- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier`
- `sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure`
- `sourcePressureIntervalPulseAddress_of_localIslandWitness`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`

These wrappers are the highest-risk extraction group because they depend on
the surrounding order-failure and bounded-diagnosis layer.

## Candidate Module Layout

### Current Compatibility Surface

Keep:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

as the compatibility surface for now.  Existing downstream imports should keep
working through this module.

### Future Low-Risk Module

Possible future module:

```text
DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
```

Potential contents:

- adjacent pair address predicate;
- adjacent diagnosis carrier;
- list-level adjacent diagnosis carrier;
- projection and propagation helpers;
- eventually bounded wrappers, but only after dependency checks.

### If Direct Extraction Is Blocked

If `PressureAdjacentDiagnosis.lean` creates an import cycle, split earlier
stable upstream declarations first.  Likely candidates:

- witness carrier and address conversion definitions;
- sorted-before failure carrier;
- adjacent-overlap obstruction carrier;
- pair recovered-budget theorem wrappers.

The bounded wrappers should move last, because they depend on the one-step and
three-/four-witness diagnosis theorems.

## Migration Plan

### Stage 1: Preflight Only

- Move no Lean declarations.
- Record dependency boundaries.
- Keep theorem names stable.
- Keep review diffs small.

This checkpoint is Stage 1.

### Stage 2: Extract Stable Low-Risk Declarations

- Extract only declarations whose dependencies already live earlier in the
  import graph.
- Keep declaration names unchanged.
- Add imports from `PressureAccounting.lean` to preserve the compatibility
  surface.
- Verify:
  - `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
  - `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
  - `lake build DkMath.Collatz.PetalBridge`

The best first extraction candidate is the adjacent-pair address predicate,
because it depends only on `SourcePressureLocalIslandWitness` and `List`.

### Stage 3: Move Carriers And Helpers

- Move `SourcePressureLocalIslandWitnessAdjacentDiagnosis` after confirming
  the overlap-obstruction and pair-budget dependencies are stable.
- Move `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis` after both
  the pair address predicate and adjacent diagnosis carrier are imported.
- Move bounded wrappers only after the carrier/address predicates are stable.

## Risks

- Import cycles if the new module imports `PressureAccounting` while
  `PressureAccounting` also imports the new module.
- Downstream files may import `PressureAccounting` and expect these names
  there.
- Bounded wrapper theorem order may depend on earlier local theorems in the
  same file.
- Namespace and name stability must be preserved; names should not change in
  the split.
- Large declaration movement can create line-number churn in review diffs.
- Moving bounded wrappers too early may pull most of `PressureAccounting` into
  the new module, defeating the split.

## Non-Goals

This refactor plan does not introduce:

- arbitrary-length classifier;
- fuel-indexed diagnosis;
- sorting;
- coverage;
- maximality;
- uniqueness;
- prefix behavior;
- union accounting;
- interval merging;
- Collatz convergence.

Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
on the enclosing list.
