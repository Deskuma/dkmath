# ABC/GN Balance Calibration — Checkpoint 002

## Scope

This report follows `instruction-002.md` and preserves the accepted Outcome A
boundaries of checkpoints 000 and 001.  The user request is “これをお願いし
ます”; the attached instruction is the bounded contract for decomposing the
pointwise calibration correction.  No exponent improvement, uniform bound,
supremum, new ABC contract, shell estimate, or optimization claim is made.

## Repository-first proof-chain audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.

The audited production proof is
`Triple.log_c_mul_pred_le_of_oddPrime_jointPressure` in
`DkMath/ABC/GNJointPressureOddPrime.lean:334`.  Its relevant source table is:

| Quantity / step | Exact current fact | Source |
|---|---|---|
| `G = Qrad + E` | equality at odd prime | `GNJointPressureOddPrime.lean:32` |
| `G = X + S + E` | equality at odd prime | `GNJointPressureOddPrime.lean:56` |
| `L = R + S` | equality for prime exponent | `GNJointPressureOddPrime.lean:240` |
| `d * H <= G` | return inequality | `GNQualityExcessBridge.lean:71` |
| `X <= P` | exceptional gauge inequality | `GNSupportReturn.lean:94` |
| `R + S <= L` | older generic transport inequality | `GNSupportReturn.lean:278` |

The old height proof uses the generic `R + S <= L` route at
`GNJointPressureOddPrime.lean:361`, but the same production file provides the
stronger prime-exponent equality `L = R + S` at line 240.  This checkpoint
therefore counts no lift-radical transport slack on the prime route.

The requested declarations were confirmed with no name mismatch:

| Declaration | Source |
|---|---|
| `GNChannelSupportMass` | `DkMath/ABC/GNBalanceCalibration.lean:30` |
| `GNChannelDepthMass` | `DkMath/ABC/GNBalanceCalibration.lean:34` |
| `GNChannelMass` | `DkMath/ABC/GNBalanceCalibration.lean:38` |
| `GNChannelBalance` | `DkMath/ABC/GNBalanceCalibration.lean:42` |
| `GNCalibrationResidual` | `DkMath/ABC/GNBalanceCalibration.lean:46` |
| `GNPointwiseCalibrationCorrection` | `DkMath/ABC/ABCBalanceCalibrationBridge.lean:30` |
| `Triple.abcEpsilon_le_GNEpsilon_add_pointwiseCalibrationCorrection` | `DkMath/ABC/ABCBalanceCalibrationBridge.lean:52` |
| `Triple.log_c_mul_pred_le_...` | `DkMath/ABC/GNJointPressureOddPrime.lean:334` |
| `Triple.log_rad_gnPowerLift_eq_...` | `DkMath/ABC/GNJointPressureOddPrime.lean:240` |

## Implemented API

The new module is
`DkMath/ABC/ABCCalibrationSourceDecomposition.lean`, importing only
`DkMath.ABC.ABCBalanceCalibrationBridge`.  It defines and proves:

- `GNReturnSlack` and its nonnegativity from the existing return theorem;
- `GNExceptionalGaugeSlack` and its nonnegativity from the existing support
  absorption theorem;
- `GNExactCalibrationCorrection`;
- `Triple.abcEpsilon_eq_GNEpsilon_add_exactCalibrationCorrection`;
- the exact decomposition
  `GNPointwiseCalibrationCorrection = GNExactCalibrationCorrection +`
  normalized return slack plus normalized gauge slack;
- the resulting monotone inequality to the accepted pointwise envelope.

The exact epsilon identity uses the existing odd-prime accounting equality,
the exact definition of return slack, and the existing
`quality_eq_one_add_abcEpsilon` normalization.  No new arithmetic hypothesis
was introduced.

## Calibration-source classification

1. `GNCalibrationResidual` is the signed mismatch between channel mass and the
   chosen slope line `rho * R`; it is not proof slack.
2. `GNChannelBalance = S - E` is not consumed by this epsilon proof and is not
   part of the correction decomposition.
3. The prime-exponent lift-radical step is exact (`L = R + S`), so it supplies
   no positive slack here.
4. `GNABCConstant`, absolute values, maxima, and exponentials belong to the
   later outer safe-envelope layer.
5. The uniform allowance `C` is absent from the exact pointwise identity; it
   appears only when the actual residual is replaced by a common upper
   allowance.

The inner GN balance remains support-minus-depth, while the outer ABC balance
has the opposite depth-minus-support orientation.  No relation between them
is introduced.

## Import and facade

`ABCCalibrationSourceDecomposition` imports the accepted bridge only, and
`DkMath.ABC` exports it once.  No historical production proof was refactored.

## Validation

Passed:

- `lake env lean DkMath/ABC/ABCCalibrationSourceDecomposition.lean`
- `lake build DkMath.ABC.ABCCalibrationSourceDecomposition`
- `lake build DkMath.ABC`
- `git diff --check`

The new module forbidden-pattern scan for `sorry`, `admit`, `axiom`, and
`unsafe` returned zero matches.  The load-bearing theorem
`DkMath.ABC.Triple.abcEpsilon_eq_GNEpsilon_add_exactCalibrationCorrection`
was audited with `#print axioms`; Lean reported only `[propext,
Classical.choice, Quot.sound]`, with no `sorryAx`.  The facade build replayed
unrelated pre-existing warnings in other modules; none came from this module.

## Outcome

Outcome A — EXACT CALIBRATION-SOURCE DECOMPOSITION COMPLETE.

The result identifies the exact correction and the two normalized
nonnegative envelope slacks, without uniformizing or optimizing them.
