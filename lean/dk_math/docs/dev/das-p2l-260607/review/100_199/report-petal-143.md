# Report Petal 143

## Scope

Checkpoint 143 performed the first import-safe split of the pressure-decay
vocabulary.

Created:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
```

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

No mathematical theorem names were changed.

## Split policy used

Moved to `PressureDecay`:

```lean
SourcePressureMarginInt

SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropInt
SourcePressureNetDropPositive

sourcePressureMarginStepDiff_eq
sourcePressureMargin_next_eq_current_add_netDrop

SourcePressureSignChangeUp
SourcePressureSignChangeDown
SourcePressureMarginJumpUp

sourcePressureMarginJumpUp_iff_stepDiff_pos
sourcePressureMarginJumpUp_of_netDropPositive
sourcePressureNetDropPositive_of_marginJumpUp
sourcePressureMarginJumpUp_iff_netDropPositive

sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls

SourcePressurePulse
SourcePressureSignPulse
sourcePressurePulse_left
sourcePressurePulse_right
sourcePressurePulse_iff_signPulse
```

Kept in `PressureFrontier`:

```lean
IsSourcePressureDepth
SelectedPressurePrefix
SourcePressurePrefixFailure
SourcePressureFrontier
SourcePressureLocalIsland
SourcePressurePositiveBlock
SourcePressureRun
SourcePressureIntervalPulse
```

and all frontier/local-island-facing bridge theorems.

## Why run/interval stayed in PressureFrontier

`SourcePressureRun` is a meaning-name alias for
`SourcePressurePositiveBlock`, and `SourcePressurePositiveBlock` depends on
`IsSourcePressureDepth`.

Moving run/interval in this checkpoint would require also moving the selected
pressure-depth layer, which would make the split larger than requested.  So
checkpoint 143 intentionally moved only the import-safe decay block and kept
run/interval vocabulary in `PressureFrontier`.

This preserves the intended dependency shape:

```text
DriftBudget
  -> PressureDecay
  -> PressureFrontier
  -> Collision / parent aggregate
```

## Public API

The parent aggregate was updated:

```lean
import DkMath.Collatz.PetalBridge.PressureDecay
import DkMath.Collatz.PetalBridge.PressureFrontier
```

So users importing:

```lean
import DkMath.Collatz.PetalBridge
```

continue to see the moved declarations.

## Python

No Python changes were needed for this checkpoint.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result:

```text
pass
```

The `rg` checks returned no matches in either split file.

The build still reports the pre-existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
```

## Inference

The first split is stable.  `PressureDecay` is now the lower layer for generic
integer pressure-margin accounting, while `PressureFrontier` remains the
frontier/island/run-facing layer.

The next checkpoint can safely return to math:

```text
SourcePressureRunAddress
SourcePressureIntervalPulseAddress
thin boundary extraction for positive runs
```

If file pressure continues, the next possible split is not more decay, but a
separate frontier/run-facing module above `PressureDecay`.
