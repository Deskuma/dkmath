# ABC/GN Balance Calibration — Checkpoint 001

## Scope

This report follows `instruction-001.md` and preserves the checkpoint-000
boundary.  The user request is “これをお願いします”; the attached
instruction is the bounded implementation contract for pointwise calibration
and outer ABC balance.  No exponent improvement, uniform calibration bound,
new ABC contract, new `K`-epsilon estimate, shell estimate, or transport
theorem is attempted.

## Repository-first audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.
Checkpoint 000 is present as Outcome A in `report-000.md`.

The requested declarations were confirmed with no name mismatch:

| Declaration | Source |
|---|---|
| `GNChannelSupportMass` | `DkMath/ABC/GNBalanceCalibration.lean:30` |
| `GNChannelDepthMass` | `DkMath/ABC/GNBalanceCalibration.lean:34` |
| `GNChannelMass` | `DkMath/ABC/GNBalanceCalibration.lean:38` |
| `GNChannelBalance` | `DkMath/ABC/GNBalanceCalibration.lean:42` |
| `GNCalibrationResidual` | `DkMath/ABC/GNBalanceCalibration.lean:46` |
| `GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le` | `DkMath/ABC/GNBalanceCalibration.lean:67` |
| `Triple.oddPrimeJointPressure_iff_calibrationResidual_le` | `DkMath/ABC/GNBalanceCalibration.lean:81` |
| `Triple.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le` | `DkMath/ABC/GNBalanceCalibration.lean:95` |
| `Triple.abcGap_eq_valuationExcess_sub_log_rad_ab` | `DkMath/ABC/ABCEpsilonIdentity.lean:67` |
| `Triple.abcGap_eq_abcEpsilon_mul_radLog` | `DkMath/ABC/ABCEpsilonIdentity.lean:95` |
| `Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc` | `DkMath/ABC/ABCEpsilonIdentity.lean:110` |
| `Triple.quality_eq_one_add_abcEpsilon` | `DkMath/ABC/ABCEpsilonIdentity.lean:121` |
| `GNEpsilon` | `DkMath/ABC/ABCEpsilonSlopeBridge.lean:26` |
| `Triple.abcEpsilon_le_GNEpsilon_add_correction` | `DkMath/ABC/ABCEpsilonSlopeBridge.lean:58` |

## Implemented API

The new bridge module is
`DkMath/ABC/ABCBalanceCalibrationBridge.lean`, importing
`DkMath.ABC.GNBalanceCalibration`.  It defines:

- `GNPointwiseCalibrationCorrection` by substituting the actual residual for
  the allowance `C` in the existing epsilon correction;
- `ABCInputSupportMass`, `ABCOutputDepthMass`, `ABCOuterMass`, and
  `ABCOuterBalance`;
- exact outer mass/balance reconstruction identities;
- `Triple.ABCOuterBalance_eq_abcGap`;
- `Triple.ABCOuterBalance_eq_abcEpsilon_mul_radLog`;
- the exact zero-contour equivalence with `abcGap`;
- the pointwise epsilon consumer and the uniform-allowance envelope theorem.

The pointwise consumer reuses
`Triple.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le`
with `C := GNCalibrationResidual T p ρ` and `le_rfl`.  No epsilon proof is
duplicated.

## Sign orientation

The inner GN coordinate remains

```text
GNChannelBalance = support mass - depth mass.
```

The outer coordinate is deliberately oriented oppositely:

```text
ABCOuterBalance = output depth mass - input support mass.
```

This is required for exact agreement with `abcGap`.  No transport or
identification between these two balances is stated.

## Import and facade

`ABCBalanceCalibrationBridge` imports only `GNBalanceCalibration`, and the
facade `DkMath.ABC` exports it once.  The existing import direction remains
acyclic.

## Validation

Passed:

- `lake env lean DkMath/ABC/ABCBalanceCalibrationBridge.lean`
- `lake build DkMath.ABC.ABCBalanceCalibrationBridge`
- `lake build DkMath.ABC`
- `git diff --check`

The new bridge module forbidden-pattern scan for `sorry`, `admit`, `axiom`,
and `unsafe` returned zero matches.  The primary theorem
`DkMath.ABC.Triple.abcEpsilon_le_GNEpsilon_add_pointwiseCalibrationCorrection`
was audited with `#print axioms`; Lean reported only `[propext,
Classical.choice, Quot.sound]`, with no `sorryAx`.  The facade build also
replayed unrelated pre-existing warnings in other modules; none came from
the new bridge.

## Outcome

Outcome A — POINTWISE CALIBRATION / OUTER BALANCE API COMPLETE.

The checkpoint stops before any supremum, uniform residual bound, new ABC
contract, exponent/constant improvement, shell estimate, Hensel transport, or
claim of contour optimality.
