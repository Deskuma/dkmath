# ABC/GN Balance Calibration — Checkpoint 003

## Scope

This report follows `instruction-003.md` and preserves the accepted Outcome A
boundaries of checkpoints 000–002.  The user request is “これをお願いしま
す”; the attached instruction is the bounded contract for local valuation
balance layers.  No exponent improvement, uniform residual bound, supremum,
new ABC contract, mutation operation, Hensel transport, or global optimality
claim is made.

## Repository-first audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.

Confirmed declarations and sources:

| Declaration | Source |
|---|---|
| `GNChannelSupportMass` | `DkMath/ABC/GNBalanceCalibration.lean:30` |
| `GNChannelDepthMass` | `DkMath/ABC/GNBalanceCalibration.lean:34` |
| `GNChannelMass` | `DkMath/ABC/GNBalanceCalibration.lean:38` |
| `GNChannelBalance` | `DkMath/ABC/GNBalanceCalibration.lean:42` |
| `GNNonExceptionalSupport` | `DkMath/ABC/GNSupportReturn.lean:30` |
| `GNNonExceptionalSupportProduct` | `DkMath/ABC/GNSupportReturn.lean:36` |
| `GNNonExceptionalValuationExcess` | `DkMath/ABC/GNValuationExcess.lean:47` |
| `GNNonExceptionalDepthSupport` | `DkMath/ABC/GNDepthPressure.lean:27` |
| `GNNonExceptionalDepthMass` | `DkMath/ABC/GNDepthPressure.lean:34` |
| `GNNonExceptionalSupportLogMass` | `DkMath/ABC/GNDepthPressure.lean:41` |
| `GNNonExceptionalValuationExcess_eq_sum_prime_depths` | `DkMath/ABC/GNDepthPressure.lean:68` |
| `GNNonExceptionalValuationExcess_eq_sum_depthMass` | `DkMath/ABC/GNDepthPressure.lean:93` |
| `GNNonExceptionalSupportLogMass_eq_log_product` | `DkMath/ABC/GNDepthPressure.lean:158` |
| `one_le_factorization_of_mem_support` | `DkMath/ABC/GNValuationExcess.lean:57` |

The prime-local factorization contribution is already exposed by
`GNValuationExcess` as `((factorization q - 1 : ℕ) : ℝ) * log q`; the new
module adds its signed local mass/balance forms without duplicating the
underlying valuation definitions.

## Implemented API

The new module is
`DkMath/ABC/GNBalanceDepthLayers.lean`.  It defines:

- `GNNonExceptionalLocalMass := v * log q`;
- `GNNonExceptionalLocalBalance := (2 - v) * log q`.

It proves:

- support mass equals the first support log layer;
- depth mass equals the finite repeated-depth layer cake;
- channel mass equals first layer plus repeated layers;
- channel balance equals first layer minus repeated layers;
- channel mass is the sum of local masses;
- channel balance is the sum of local signed balances;
- the exact local pivot and sign consequences for valuation depths `1`, `2`,
  and at least `3`.

The load-bearing global sum theorem is
`GNChannelBalance_eq_sum_nonExceptionalLocalBalance`.

## Local interpretation and boundary

For `v = 1`, the local balance is `+ log q` (support-heavy).  For `v = 2`,
it is exactly `0` (the local pivot).  For `v >= 3`, it is strictly negative
(depth-heavy).  These are local consequences of the signed coefficient and
prime/log positivity.

The module does not claim that the global zero contour forces every local
valuation to equal `2`: positive and negative local contributions may cancel.
It also does not compare distinct triples or encode a mutation operation.

The checkpoint-000 inner balance remains `support - depth`; the checkpoint-001
outer ABC balance remains `depth - support`.  No relation between them is
introduced.

## Import and facade

`GNBalanceDepthLayers` imports the accepted calibration decomposition and
`GNDepthPressure`; `DkMath.ABC` exports the new module once.  Historical
production files were not refactored.

## Validation

All requested focused validations passed:

- `lake env lean DkMath/ABC/GNBalanceDepthLayers.lean`
- `lake build DkMath.ABC.GNBalanceDepthLayers`
- `lake build DkMath.ABC`
- `git diff --check`
- forbidden-pattern scan on the new module for `sorry`, `admit`, `axiom`, and
  `unsafe`: no matches;
- trailing-whitespace scan on the new module and this report: no matches.

The load-bearing theorem audit was run with `#print axioms` on
`GNChannelBalance_eq_sum_nonExceptionalLocalBalance`; Lean reported only
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.  The facade
build also replayed the repository's pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`; it is outside this
checkpoint's new module.

## Outcome

Outcome A — the required first/repeated-layer decomposition, exact signed
prime-local balance sum, valuation-two zero pivot, and local sign consequences
are kernel-checked and exported through `DkMath.ABC`.  No stronger global
claim is included.
