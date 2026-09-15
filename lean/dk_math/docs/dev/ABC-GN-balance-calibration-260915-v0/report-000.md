# ABC/GN Balance Calibration — Checkpoint 000

## Scope

This report follows `CODEX_START.md`, `README.md`, and `instruction-000.md`.
The user request is to continue formalizing the ABC balance; the attached
documents bound this turn to exact coordinate extraction and calibration
equivalences.  No exponent improvement, uniform residual bound, new ABC
contract, shell estimate, or optimality claim is included.

## Repository-first audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.

The requested `SUMMARY.md` was not present in this checkout.  The other
requested documents were found and read.  The exact production declarations
are:

| Declaration | Source |
|---|---|
| `Triple.abcGap_eq_valuationExcess_sub_log_rad_ab` | `DkMath/ABC/ABCEpsilonIdentity.lean:67` |
| `Triple.abcGap_eq_abcEpsilon_mul_radLog` | `DkMath/ABC/ABCEpsilonIdentity.lean:95` |
| `Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc` | `DkMath/ABC/ABCEpsilonIdentity.lean:110` |
| `Triple.quality_eq_one_add_abcEpsilon` | `DkMath/ABC/ABCEpsilonIdentity.lean:121` |
| `GNNonExceptionalSupportProduct` | `DkMath/ABC/GNSupportReturn.lean:36` |
| `GNNonExceptionalValuationExcess` | `DkMath/ABC/GNValuationExcess.lean:47` |
| `GNOddPrimeJointPressureBudgetAffine` | `DkMath/ABC/GNJointPressureOddPrime.lean:90` |
| `GNNonExceptionalChannelMassBudgetAffine` | `DkMath/ABC/GNJointPressureOddPrime.lean:261` |
| `Triple.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess` | `DkMath/ABC/GNJointPressureOddPrime.lean:48` |
| `Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime` | `DkMath/ABC/GNJointPressureOddPrime.lean:240` |
| `Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass` | `DkMath/ABC/GNJointPressureOddPrime.lean:296` |
| `Triple.log_c_mul_pred_le_of_oddPrime_jointPressure` | `DkMath/ABC/GNJointPressureOddPrime.lean:334` |
| `GNEpsilon` | `DkMath/ABC/ABCEpsilonSlopeBridge.lean:26` |
| `GNEpsilon_le_iff_margin` | `DkMath/ABC/ABCEpsilonSlopeBridge.lean:33` |
| `Triple.abcEpsilon_le_GNEpsilon_add_correction` | `DkMath/ABC/ABCEpsilonSlopeBridge.lean:58` |
| `GNABCConstant` | `DkMath/ABC/GNFinalBudgetBridge.lean:92` |
| `ABCGNOddPrimeJointContract` | `DkMath/ABC/GNJointPressureOddPrime.lean:436` |
| `abc_positive_of_GNOddPrimeJointContract` | `DkMath/ABC/GNJointPressureOddPrime.lean:450` |
| `abc_of_GNOddPrimeJointContract` | `DkMath/ABC/GNJointPressureOddPrime.lean:470` |

There were no declaration-name mismatches among the requested production
names.  `GNOddPrimeJointPressureBudgetAffine` is also recorded because it is
the left-hand side of the load-bearing equivalence.

## Import direction

The relevant imports are:

```text
ABCEpsilonIdentity
  -> GNQualityExcessBridge and SquareTailGapIdentity
GNJointPressureOddPrime
  -> GNExceptionalExcessOddPrime
ABCEpsilonSlopeBridge
  -> ABCEpsilonIdentity and GNJointPressureOddPrime
```

`GNBalanceCalibration` imports `ABCEpsilonSlopeBridge`.  This adds no cycle:
the slope bridge does not import the new module.  The public `DkMath.ABC`
facade exports the new module once.

## Implemented API

The new module `DkMath/ABC/GNBalanceCalibration.lean` defines:

- `GNChannelSupportMass` as the fresh non-exceptional support log mass;
- `GNChannelDepthMass` as the non-exceptional valuation excess;
- `GNChannelMass` as their sum;
- `GNChannelBalance` as their difference;
- `GNCalibrationResidual` as `GNChannelMass - ρ * T.radLog`.

It proves both exact reconstruction identities, the equivalence
`GNNonExceptionalChannelMassBudgetAffine T p ρ C ↔
GNCalibrationResidual T p ρ ≤ C`, and the load-bearing theorem
`Triple.oddPrimeJointPressure_iff_calibrationResidual_le` by composing the
existing production equivalences.  The optional epsilon consumer theorem is
also included by transporting the residual hypothesis back to the existing
`Triple.abcEpsilon_le_GNEpsilon_add_correction` theorem.

## Validation

Passed:

- `lake env lean DkMath/ABC/GNBalanceCalibration.lean`
- `lake build DkMath.ABC.GNBalanceCalibration`
- `lake build DkMath.ABC`
- `git diff --check`

The new module forbidden-pattern scan for `sorry`, `admit`, `axiom`, and
`unsafe` returned zero matches.  The load-bearing theorem
`DkMath.ABC.Triple.oddPrimeJointPressure_iff_calibrationResidual_le` was
audited with `#print axioms`; Lean reported only `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`.  The facade build also replayed unrelated
pre-existing warnings in other modules; none came from the new module.

## Outcome

Outcome A — EXACT BALANCE/CALIBRATION API COMPLETE.

The checkpoint stops at exact coordinate identities and transport of existing
production bounds.  It does not claim a uniform residual bound, a new ABC
contract, a better exponent, or optimality of the zero-balance contour.
