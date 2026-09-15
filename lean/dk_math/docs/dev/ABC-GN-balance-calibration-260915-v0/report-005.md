# ABC/GN Balance Calibration — Checkpoint 005

## Scope and outcome

This report treats `instruction-005.md` as the bounded checkpoint contract.
The implementation completes the exceptional cubic bookkeeping around the
existing BCAL balance coordinate.  It does not add estimates, uniform bounds,
Hensel transport, mutation, monotonicity, optimality, shell counting, an ABC
closure, or a new axiom.

Outcome A — EXACT EXCEPTIONAL COMPLETION.  The full cubic complement is
factored into the exceptional single-layer product and the non-exceptional
single layer.  The exceptional prime has valuation zero or one, so it does
not affect `twoTail`.  The resulting unconditional logarithmic bridge and its
existing gauge-slack form are kernel checked.

## Source audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.

The implementation reuses the existing APIs requested by the checkpoint:

| Item | Existing source and use |
|---|---|
| cubic depth exclusion | `DkMath/ABC/GNExcessCubicComplement.lean:39`; `9 ∤ GN 3 a 1` |
| non-exceptional repeated part | `.../GNExcessCubicComplement.lean:49`; reused in the full-complement proof |
| full cubic complement | `.../GNExcessCubicComplement.lean:150`; definition retained |
| exceptional gauge slack | `DkMath/ABC/ABCCalibrationSourceDecomposition.lean:36`; reused without a new correction definition |
| exact calibration correction | `.../ABCCalibrationSourceDecomposition.lean:42`; already contains `log exceptionalSupportProduct` |
| odd-prime exceptional excess | `DkMath/ABC/GNExceptionalExcessOddPrime.lean:31`; confirms the same exceptional coordinate is a valuation-excess-neutral gauge coordinate |

The production implementation is in
`DkMath/ABC/GNBalanceCubicShell.lean`, and it is exported by
`DkMath/ABC.lean:56`.

## Exact exceptional arithmetic

For `F(a) = GN 3 a 1 = a^2 + 3*a + 3`, the theorem
`GN_cubic_three_factorization_eq_one_of_dvd` (`GNBalanceCubicShell.lean:206`)
proves

```text
3 ∣ F(a) -> F(a).factorization 3 = 1.
```

It uses the existing `not_nine_dvd_GN_three_one_value`, so the cubic
exceptional valuation is zero or one and never at least two.

The exact support product is exposed by
`GNExceptionalSupportProduct_three_one_eq_if`
(`GNBalanceCubicShell.lean:276`):

```text
GNExceptionalSupportProduct 3 a 1
  = if 3 ∣ GN 3 a 1 then 3 else 1.
```

The support/factorization proof then establishes
`GN_cubic_eq_exceptional_mul_nonExceptionalPart`
(`GNBalanceCubicShell.lean:316`), followed by the preferred exact complement
identity:

```text
GNExcessCubicComplement a
  = GNExceptionalSupportProduct 3 a 1
    * GNNonExceptionalSingleLayer 3 a 1.
```

This is `GNExcessCubicComplement_eq_exceptional_mul_nonExceptionalSingleLayer`
at `GNBalanceCubicShell.lean:374`.  It is proved through factorization,
support partition, and the existing repeated-part equality; it is not inferred
from the names of the definitions.

## `twoTail` compatibility

`twoTail_GN_cubic_eq_twoTail_nonExceptionalPart`
(`GNBalanceCubicShell.lean:396`) proves the unconditional identity

```text
twoTail (GN 3 a 1)
  = twoTail (GNNonExceptionalPart 3 a 1).
```

The exceptional support can only be `{3}`, and its factorization exponent is
one whenever present.  Its contribution to the `v - 2` tail exponent is
therefore zero.

## Unconditional balance bridge

The central theorem is
`GNChannelBalance_cubic_eq_log_fullComplement_sub_log_twoTail_sub_log_exceptional`
(`GNBalanceCubicShell.lean:444`):

```text
GNChannelBalance (Triple.mk a 1 (a + 1) ...) 3
  = log (GNExcessCubicComplement a)
    - log (twoTail (GN 3 a 1))
    - log (GNExceptionalSupportProduct 3 a 1).
```

Thus the discrepancy in the full cubic complement is exactly the exceptional
single-layer log mass.  No inequality or estimate is used.

The gauge rewrite is
`GNChannelBalance_cubic_eq_fullShell_sub_radLog_add_gaugeSlack`
(`GNBalanceCubicShell.lean:481`):

```text
GNChannelBalance
  = (log fullComplement - log twoTail) - log (rad 3)
    + GNExceptionalGaugeSlack T 3.
```

This follows by unfolding the existing
`GNExceptionalGaugeSlack`; since `rad 3 = 3`, it is exactly the requested
BCAL-002 coordinate and not a new independent cubic correction.

## Recovery of BCAL-004 and calibration relation

The earlier conditional theorem
`GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail`
(`GNBalanceCubicShell.lean:258`) is preserved.  The new corollary
`GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail_recovered`
(`GNBalanceCubicShell.lean:472`) derives the same formula from the
unconditional bridge when `¬ 3 ∣ GN 3 a 1`, because the exceptional product is
then `1`.

The exact calibration definition
`GNExactCalibrationCorrection` already contains
`Real.log (GNExceptionalSupportProduct p T.a T.b)` directly in its numerator
(`ABCCalibrationSourceDecomposition.lean:42-47`).  Consequently the same
exceptional log is simultaneously the missing full-shell coordinate here and
the existing BCAL-002 calibration term.  No new epsilon identity or new ABC
contract was introduced.

The odd-prime theorem
`Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime`
(`GNExceptionalExcessOddPrime.lean:31`) is consistent with this reading: the
exceptional prime contributes a single-layer gauge coordinate, not repeated or
over-depth mass.

## Boundary and next checkpoint value

BCAL-004 Outcome B is fully resolved at the exact arithmetic level: its
obstruction was the omitted exceptional single layer, and BCAL-005 records
that term explicitly.  No Hensel or depth-step transport is justified by this
bookkeeping.  A later checkpoint may study such transport only with separate
hypotheses and a separately audited finite API.

No estimate, counting theorem, provider, global density statement, ABC
closure, RH consequence, mutation theorem, monotonicity claim, or optimality
claim follows from the present module.

## Validation

The following validations passed in the nested Lake project
`lean/dk_math`:

- `lake env lean DkMath/ABC/GNBalanceCubicShell.lean`
- `lake build DkMath.ABC.GNBalanceCubicShell`
- `lake build DkMath.ABC`
- `#print axioms` audit for the new exact exceptional, `twoTail`, balance,
  recovered-conditional, and gauge theorems: only
  `[propext, Classical.choice, Quot.sound]`
- forbidden-token scan of the new production module for `sorry`, `admit`,
  `axiom`, and `unsafe`: no matches
- trailing-whitespace scan: no matches
- `git diff --check`: passed

The facade build replayed the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` (`sorry`), outside
this checkpoint and unrelated to the new module.
