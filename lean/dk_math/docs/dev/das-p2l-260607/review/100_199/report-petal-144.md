# Report Petal 144

## Scope

Checkpoint 144 returned to the mathematical API after the `PressureDecay`
split.  It added a thin address layer for positive pressure runs and interval
pulses.

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

No Python changes were needed.

## Lean additions

Added run address:

```lean
structure SourcePressureRunAddress (n : OddNat) (k r : Nat)
```

Fields:

```lean
start : Nat
len   : Nat
hrun  : SourcePressureRun n k r start len
```

Added interval-pulse address:

```lean
structure SourcePressureIntervalPulseAddress (n : OddNat) (k r : Nat)
```

Fields:

```lean
start  : Nat
len    : Nat
hpulse : SourcePressureIntervalPulse n k r start len
```

Added address helpers:

```lean
SourcePressureRunAddress.depthStart
SourcePressureRunAddress.depthEnd
SourcePressureIntervalPulseAddress.toRunAddress
```

Added interval-pulse address projections:

```lean
sourcePressureIntervalPulseAddress_left_signChange
sourcePressureIntervalPulseAddress_right_signChange
```

Added local-island address constructor:

```lean
def sourcePressureIntervalPulseAddress_of_localIsland
```

## Design note

The address layer is intentionally only a witness package:

```text
relative start
length
run / pulse proof
```

It does not assert maximality, uniqueness, coverage, or prefix behavior.

The absolute depth helpers are:

```lean
depthStart := r + A.start
depthEnd   := r + (A.start + A.len - 1)
```

This keeps the pressure-depth index convention visible:

```text
r = base pressure depth
start = relative depth offset
len = run length
```

## Inference

The useful shape now is:

```text
SourcePressureLocalIsland
  -> SourcePressureIntervalPulse n k r j 1
  -> SourcePressureIntervalPulseAddress n k r
  -> SourcePressureRunAddress n k r
```

This gives later checkpoints a stable object to pass around without repeatedly
threading explicit `start`, `len`, and proof fields.

The next mathematical layer can add projections from addresses to:

```text
absolute start/end depths
left/right sign changes
left/right net-drop crossing/falling
```

or split address vocabulary into a small `PressureAddress` module if
`PressureFrontier` continues growing.

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

The `rg` checks returned no matches in either file.

The build still reports the pre-existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
```

## Suggested next checkpoint

Add address projection helpers:

```lean
sourcePressureIntervalPulseAddress_toRun
sourcePressureIntervalPulseAddress_left_crossing
sourcePressureIntervalPulseAddress_right_falling
SourcePressureIntervalPulseAddress.depthStart
SourcePressureIntervalPulseAddress.depthEnd
```

Keep the same rule: address helpers only, no maximality or uniqueness.
