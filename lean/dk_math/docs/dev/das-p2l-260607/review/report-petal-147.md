# report-petal-147

Date: 2026-07-04

## Checkpoint

Follow-up implementation after checkpoint 146.

Checkpoint 146 proved that an interval-pulse address has a negative accumulated
net pressure drive.  This follow-up extracts stronger and more reusable
accounting consequences from the same proof state.

No maximality, uniqueness, coverage, prefix behavior, or Collatz convergence is
introduced.

## Code Changes

Updated:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`

Added algebraic/accounting corollaries:

- `sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start`
- `sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin`
- `sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos`
- `sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one`

Added bundled observation profiles:

- `sourcePressureIntervalPulseAddress_endpoint_profile`
- `sourcePressureIntervalPulseAddress_accounting_profile`

## Resulting Reading

The prior theorem said:

```text
sum netDrop < 0
```

The new theorems make the reason explicit:

```text
sum netDrop = afterMargin - startMargin
afterMargin <= 0
startMargin > 0
therefore sum netDrop <= -startMargin <= -1
```

This is stronger than just proving negativity.  It says that the interval must
pay at least the whole positive starting margin.

## Why This Helps

Later finite-budget arguments usually prefer non-strict inequalities over
strict inequalities.  The new theorem

```lean
sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
```

turns strict integer negativity into a budget-friendly `<= -1` form.

The theorem

```lean
sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
```

is more informative: it records how much pressure must be cancelled by the
finite interval drive.

The bundled profile theorems are deliberately just projection conveniences.
They let downstream code unpack one address object into the endpoint signs and
accounting facts without repeatedly reopening the pulse construction.

## Verification

Passed:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- `lake build DkMath.Collatz.PetalBridge`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
- `git diff --check`

The `rg` command returned no matches.  The aggregate build still reports the
pre-existing unrelated warning that
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
`sorry`.

## Next Implementation Candidates

The next useful layer is probably a named local carrier:

```lean
def SourcePressureAccountedInterval ...
```

This should remain thin and local.  It can package:

- the address,
- endpoint profile,
- accumulated drive identity,
- accumulated drive budget bound.

Alternatively, if the next review prefers theorem-only growth, add list/finite
family versions that sum over explicitly provided addresses.  That route should
still avoid coverage and maximality claims unless they are separately proved.
