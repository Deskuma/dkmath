# report-petal-219

## Checkpoint

`petal-219`

## Goal

Investigate whether interval-pulse addresses can be connected to the Beam
mass-balance API at exact edges.

The cp218 result established the direct local route:

```text
signChangeUp   -> left < right
signChangeDown -> right <= left
```

This checkpoint checks whether the interval-pulse address layer supplies those
sign-change inputs.

## Definitions and theorems inspected

### `SourcePressureIntervalPulse`

Located in `PressureFrontier`.

It packages:

```lean
SourcePressureRun n k r a len
SourcePressureRunHasLeftCrossing n k r a len
SourcePressureRunHasRightFall n k r a len
```

The important boundary predicates are:

```lean
SourcePressureRunHasLeftCrossing n k r a len
  = 0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)

SourcePressureRunHasRightFall n k r a len
  = SourcePressureSignChangeDown n k r (a + len - 1)
```

### `SourcePressureIntervalPulseAddress`

Located in `PressureFrontier`.

It stores:

```lean
start : Nat
len   : Nat
hpulse : SourcePressureIntervalPulse n k r start len
```

The exact edge shapes are therefore:

```text
left edge  = A.start - 1
right edge = A.start + A.len - 1
```

### Existing exact-edge sign-change API

Already available:

```lean
sourcePressureIntervalPulseAddress_left_signChange
sourcePressureIntervalPulseAddress_right_signChange
```

These are stronger than just net-drop positivity/negativity.  They directly
supply:

```lean
SourcePressureSignChangeUp n k r (A.start - 1)
SourcePressureSignChangeDown n k r (A.start + A.len - 1)
```

The `PressureAccounting` lemmas:

```lean
sourcePressureIntervalPulseAddress_left_netDrop_pos
sourcePressureIntervalPulseAddress_right_netDrop_neg
```

are useful derived facts, but the sign-change bridge was already present in
the upstream address layer.

## Lean changes

File changed:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
```

Added exact-edge interval-pulse bridge comments and four theorems:

```lean
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
theorem sourcePressureMargin_next_pos_of_intervalPulse_left
theorem sourcePressureMargin_next_nonpos_of_intervalPulse_right
```

These are all exact-edge local statements.  They do not transport arbitrary
targets, aggregate interval families, repair overlap, or claim coverage.

## Classification

### True Beam

An interval-pulse address supplies a True Beam inequality at its exact left
edge:

```lean
SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
  SourcePressureBeamMassBalanceRightInt n k r (A.start - 1)
```

provided the Beam addressed-target carrier is also supplied at that same edge:

```lean
SourcePressureBeamAddressedDepthTarget L (A.start - 1)
```

### False Beam / Boundary

An interval-pulse address supplies the non-strict false/boundary comparison at
its exact right edge:

```lean
SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
  SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1)
```

provided the Beam addressed-target carrier is also supplied at that same edge:

```lean
SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)
```

This is non-strict because the right boundary stores
`SourcePressureSignChangeDown`, which says the next margin is nonpositive.
Strict false still requires a strictly negative next margin.

### Boundary

No new equality-specific upstream source was added.  The equality boundary
remains the existing mass-balance equality API in `PressureBeam`.

### Gap

The remaining gap is not interval-pulse-to-sign-change.  That bridge already
exists.

The remaining gap is address alignment:

```text
interval-pulse exact edge
  and
Beam addressed target edge
```

must be supplied for the same index.  This is intentional: the theorem should
not invent target transport or claim that every pulse edge is automatically a
Beam addressed target.

## Verification

Commands run:

```bash
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry grep over inspected files: no matches.
- `git diff --check`: passed.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next candidate

The next natural bridge is not another local classifier.  The classifier now
accepts:

```text
local island
interval pulse address
sign change
```

The next useful question is whether witness-derived pulse addresses can supply
the required Beam addressed-target carrier at the same exact edge, without
claiming global coverage.

Candidate direction:

```text
local-island witness
  -> interval-pulse address
  -> exact left/right edge
  -> addressed Beam target at the same edge
```

This should remain an explicit witness/edge theorem, not a family coverage or
canonical target selection theorem.
