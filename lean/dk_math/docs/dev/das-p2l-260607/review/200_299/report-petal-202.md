# report-petal-202

## Checkpoint

`petal-202` started as an audit-only checkpoint, then continued with the
small implementation that the audit recommended.

The first safe index axis for Beam transport above `PressureBeam` was audited,
and the resulting thin depth-indexed target was added to `PressureBeam.lean`.

## Current Beam Boundary

`PressureBeam` currently contains only:

- `SourcePressureBeamSeed`
- `sourcePressureBeamSeed_of_sortedBeforeFailure`
- `sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap`
- `SourcePressureBeamDepthTarget`
- `sourcePressureBeamDepthTarget_iff_margin_pos`

These are Beam-facing names for the local `PressureAutomaton` state.  They do
not propagate anything yet.  `SourcePressureBeamDepthTarget` is only the
Beam-facing depth target name for `IsSourcePressureDepth`.

The import direction remains:

```text
PressureAutomaton
  <- PressureBeam
```

## Axis Audit

### 1. Pressure-depth index

Candidate axis:

```lean
(n : OddNat) (k r j : ℕ)
```

Existing exposure:

- `PressureDecay`
  - `SourcePressureMarginInt n k (r + j)`
  - `SourcePressureNetDropInt n k r j`
  - `SourcePressureSignChangeUp n k r j`
  - `SourcePressureSignChangeDown n k r j`
  - `SourcePressurePulse n k r j`
- `PressureFrontier`
  - `IsSourcePressureDepth n k r j`
  - `SourcePressurePrefixFailure n k r j₁ j₂`
  - selected-depth extraction theorems from finite depth ranges
- `PressureAccounting`
  - `SourcePressureIntervalNetDrop n k r start len`
  - interval-address facts whose endpoints are expressed in depth coordinates

This axis is already explicit and local.  It supports thin facts without
claiming coverage, aggregation, or convergence.

Assessment: safest first Beam axis.

### 2. Orbit-time index

Candidate axis:

```lean
(n : OddNat) (k : ℕ)
```

Existing exposure:

- The mass and count functions are orbit-window based, so `k` is present in
  almost every pressure definition.
- However, the pressure decomposition currently reasons about a fixed window
  and fixed base depth `r`.
- No existing Beam theorem transports a local automaton state from time `k` to
  time `k + 1`.

Orbit-time transport is conceptually important, but it would immediately ask
for a real propagation theorem.  That is too strong for the first Beam
checkpoint.

Assessment: important later, not first.

### 3. Witness-list / interval-address index

Candidate axis:

```lean
L : List (SourcePressureLocalIslandWitness n k r)
A : SourcePressureIntervalPulseAddress n k r
start len : ℕ
```

Existing exposure:

- `PressureAccounting` converts explicit local-island witnesses into
  interval-pulse addresses.
- It also owns sorted-before/failure predicates for explicit witness lists.
- `PressureAutomaton` and `PressureBeam` already consume a witness list `L`.

This axis is good for accounting, diagnostics, and obstruction handling.
However, using it as the first Beam transport axis risks turning the first
Beam theorem into list recursion, aggregation, or interval union accounting.
Those are explicitly out of scope.

Assessment: useful after the depth-indexed target is named, not first.

## Recommendation

Use pressure-depth indexing first.

Reason:

- It is already the native axis of `PressureDecay`.
- It is the axis on which local margins, net drops, sign changes, and pulses
  are stated.
- It can support a thin Beam predicate without requiring coverage,
  aggregation, global propagation, or convergence.
- It keeps the first Beam transport statement local and checkable.

## Proposed Next Lean Shape

The first Beam target should be a predicate, not a structure.

Reason:

- A structure would suggest accumulated transport data before the transport
  relation is known.
- A theorem would be premature because no transport target has been fixed yet.
- A predicate gives the next checkpoint a named surface without overclaiming.

Implemented definition:

```lean
/--
Depth-indexed Beam target for a local pressure seed.

This is only a named target at one explicit relative pressure depth.  It does
not assert that a seed reaches this target, that targets cover a range, or that
targets aggregate across a Beam.
-/
def SourcePressureBeamDepthTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j
```

This required `PressureBeam` to continue importing only
`PressureAutomaton`, because `IsSourcePressureDepth` is already available
through the import chain.

Implemented thin theorem:

```lean
theorem sourcePressureBeamDepthTarget_iff_margin_pos
    (n : OddNat) (k r j : ℕ) :
    SourcePressureBeamDepthTarget n k r j ↔
      0 < SourcePressureMarginInt n k (r + j)
```

This theorem is safe because it is just the Beam-facing spelling of
`isSourcePressureDepth_iff_margin_pos`.

Do not yet prove:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

That would be a real transport theorem and needs a precise relation between
the seed list and the target depth.

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

## Next Checkpoint

The next checkpoint should not repeat the depth-target naming work; it is now
implemented.  The next safe step is to define an explicit seed-to-depth
relation shape before proving any transport theorem.  In particular, avoid a
statement of the form

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

until the relation between the seed list `L` and the target depth `j` is
supplied explicitly.
