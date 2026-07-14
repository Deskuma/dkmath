# report-petal-145

Date: 2026-07-03

## Checkpoint

Implemented the address-projection layer requested in
`__next_implementation-145.md`.

This checkpoint keeps the `PressureFrontier` layer focused on finite
addressable pressure intervals.  The new API does not introduce maximality,
uniqueness, coverage, prefix, or convergence claims.  It only makes the data
already carried by `SourcePressureIntervalPulseAddress` easier to project and
reuse.

## Code Changes

Updated:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`

Added run-address helpers:

- `SourcePressureRunAddress.len_pos`

Added interval-pulse-address helpers:

- `SourcePressureIntervalPulseAddress.len_pos`
- `SourcePressureIntervalPulseAddress.depthStart`
- `SourcePressureIntervalPulseAddress.depthEnd`
- `sourcePressureIntervalPulseAddress_start_pos`
- `sourcePressureIntervalPulseAddress_toRun`
- `sourcePressureIntervalPulseAddress_toRun_depthStart`
- `sourcePressureIntervalPulseAddress_toRun_depthEnd`
- `sourcePressureIntervalPulseAddress_left`
- `sourcePressureIntervalPulseAddress_right`
- `sourcePressureIntervalPulseAddress_left_crossing`
- `sourcePressureIntervalPulseAddress_right_falling`

The existing sign-change projection lemmas now route through the new left/right
boundary projections:

- `sourcePressureIntervalPulseAddress_left_signChange`
- `sourcePressureIntervalPulseAddress_right_signChange`

## Design Notes

The practical value of this checkpoint is that later arguments can work from an
address object and then recover:

- the positive interval length,
- the absolute pressure-depth endpoints,
- the forgotten run address,
- the left crossing boundary,
- the right falling boundary,
- and the net-drop form of both boundaries.

This makes the address object usable as a compact carrier for future interval
accounting.  A later proof can quantify over an address once, then pull out the
local algebraic facts without reopening the underlying pulse constructor.

One implementation detail was corrected during verification: the forgetful
projection `sourcePressureIntervalPulseAddress_toRun` is a `def`, not a
`theorem`, because its target is a structure rather than a proposition.

## Verification

Passed:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- `lake build DkMath.Collatz.PetalBridge`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
- `git diff --check`

The two `rg` commands returned no matches.  The aggregate build still reports
the pre-existing unrelated warning that
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
`sorry`.

## Next Implementation Candidates

The next natural step is to use these projections to state a small
address-level accounting theorem.  Good candidates are:

- a bundled theorem exposing both endpoint depths and both boundary witnesses,
- a one-line bridge from interval-pulse addresses to net-drop interval data,
- or a finite-list collection layer for pressure addresses, if the next review
turn asks for interval enumeration.

The safe path is to keep the next addition thin: project existing facts from
the address carrier before adding any new global pressure principle.
