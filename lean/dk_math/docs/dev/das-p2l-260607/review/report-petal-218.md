# report-petal-218

## Checkpoint

`petal-218`

## Goal

Investigate where the addressed Beam mass-balance inequality can come from
upstream.

The local classifier is already closed in `PressureBeam`:

```lean
nextMargin = right - left
```

and cp217 packages the local trichotomy:

```text
positive / zero / negative
paired with
left < right / left = right / right < left
```

This checkpoint therefore asks for upstream sources of:

```lean
SourcePressureBeamMassBalanceLeftInt n k r j <
  SourcePressureBeamMassBalanceRightInt n k r j
```

or the boundary / false-side alternatives.

## Modules inspected

### `DkMath.Collatz.PetalBridge.DriftBudget`

This module contains global and semi-global drift-budget facts:

- two-layer and three-layer drift lower bounds;
- prefix drift budgets;
- residue-address drift bridges;
- delayed depth-two / tail-reservoir budgets.

These are useful for later pressure-budget work, but they do not directly
supply the addressed edge-local inequality

```lean
left < right
```

for an arbitrary `SourcePressureBeamAddressedDepthTarget L j`.

Classification: `Gap` for immediate local Beam input.

### `DkMath.Collatz.PetalBridge.PressureDecay`

This module provides the key edge-local sign-change vocabulary:

- `SourcePressureSignChangeUp`
- `SourcePressureSignChangeDown`
- `SourcePressureMarginJumpUp`
- `SourcePressureNetDropPositive`
- margin transition identities.

These predicates are exactly local to one adjacent pressure-depth edge, so
they are compatible with the addressed Beam classifier.

Classification:

- `True Beam`: upward sign change gives next-margin positivity.
- `False Beam / Boundary`: downward sign change gives next-margin nonpositivity.

### `DkMath.Collatz.PetalBridge.PressureFrontier`

This module connects local islands to sign changes:

- `sourcePressureSignChangeUp_of_localIsland`
- `sourcePressureSignChangeDown_of_localIsland`
- `sourcePressureNetDropPositive_of_localIsland_left`
- `sourcePressureCrosses_of_localIsland_left`
- `sourcePressureFalls_of_localIsland_right`

This gives a concrete upstream source for Beam comparisons:

- the left edge of a local island is a True Beam source;
- the right edge of a local island is a False/Boundary source.

Classification:

- `True Beam`: local-island left edge.
- `False Beam / Boundary`: local-island right edge.

### `DkMath.Collatz.PetalBridge.PressureAccounting`

This module provides interval-pulse and list/family accounting:

- `sourcePressureIntervalPulseAddress_left_netDrop_pos`
- `sourcePressureIntervalPulseAddress_right_netDrop_neg`
- interval net-drop negativity;
- sorted-family sum bounds;
- accounted interval budgets.

These are strong future inputs, but they are interval/list level.  They do not
directly become a mass-balance inequality at an arbitrary addressed `j`
without choosing the corresponding edge address.

Classification: promising `Gap` toward future interval-to-Beam edge bridges.

### `PressureLocalWitnessObstruction`, `PressureAdjacentDiagnosis`, `PressureDiagnosticDecomposition`

These modules organize witness-list order failures, overlap obstructions, and
bounded adjacent diagnosis.  They are intentionally local to explicit witness
lists and adjacent pairs.

They do not provide a global inequality source, but they can select explicit
witness-derived edges.  That matches the project guardrail: no global coverage,
no arbitrary target transport, no overlap repair.

Classification: witness-selection infrastructure, not direct inequality.

## Lean changes

File changed:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
```

Added a code-comment research note and four thin bridge theorems:

```lean
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
theorem sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
theorem sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
```

These theorems do not add propagation.  They only feed existing upstream
edge-local predicates into the already-closed Beam mass-balance classifier.

## Classification of findings

### True Beam

An upward sign change at the same addressed edge gives:

```lean
SourcePressureBeamMassBalanceLeftInt n k r j <
  SourcePressureBeamMassBalanceRightInt n k r j
```

Local-island left edges provide this upstream condition through
`sourcePressureSignChangeUp_of_localIsland`.

### Boundary

The exact equality boundary remains the existing cp216 API:

```lean
SourcePressureBeamMassBalanceLeftInt n k r j =
  SourcePressureBeamMassBalanceRightInt n k r j
```

No new upstream equality source was found in this checkpoint.

### False Beam

A downward sign change at the same addressed edge gives the non-strict
False/Boundary comparison:

```lean
SourcePressureBeamMassBalanceRightInt n k r j ≤
  SourcePressureBeamMassBalanceLeftInt n k r j
```

Local-island right edges provide this upstream condition through
`sourcePressureSignChangeDown_of_localIsland`.

The strict false branch still requires the existing stricter next-margin
negative input:

```lean
sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
```

### Gap

No aggregate theorem in `DriftBudget` or `PressureAccounting` currently
supplies `left < right` for an arbitrary addressed target.  The next viable
route is an explicit edge bridge:

```text
interval-pulse address / local witness edge
  -> sign-change or next-margin sign at that exact edge
  -> Beam mass-balance comparison
```

This should remain edge-local unless a later theorem supplies a precise
coverage or disjointness hypothesis.

## Verification

Commands run:

```bash
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/DriftBudget.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry grep over the inspected pressure files: no matches.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next candidate

The next natural checkpoint is to connect interval-pulse addresses more
directly to the Beam mass-balance API.

Candidate shapes:

```lean
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
theorem sourcePressureBeamMassBalanceRight_lt_left_of_intervalPulse_right
```

These should require an addressed target at exactly the pulse edge:

```text
left edge:  A.start - 1
right edge: A.start + A.len - 1
```

This would keep the route local and avoid any claim about arbitrary target
transport or global family coverage.
