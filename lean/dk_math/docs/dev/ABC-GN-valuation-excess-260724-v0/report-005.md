# Report 005: unconditional GN return and high-lift carriers

## Outcome

Outcome A is complete:

```text
unconditional GN return: closed
quality-to-excess: reduced to support budget only
valuation excess: exact finite high-lift carrier sum
```

## Natural and logarithmic GN return

`DkMath/ABC/GNPowerLift.lean` adds:

```text
Triple.pow_pred_c_le_GN
```

Under `1 ≤ n` and `0 < T.a`, it proves
`T.c^(n-1) ≤ GN n T.a T.b`.  The proof uses Route 2.  From `T.b ≤ T.c` it
gets `T.b^n ≤ T.b * T.c^(n-1)`, combines this with
`T.a * GN + T.b^n = T.c^n`, rewrites `T.c = T.a + T.b`, and cancels the
positive factor `T.a`.  No natural-number division is used.

`DkMath/ABC/GNQualityExcessBridge.lean` adds:

```text
Triple.log_c_mul_pred_le_log_GN
Triple.gnReturnLowerBound_pred
```

Thus `GNReturnLowerBound T n (n-1)` is fully discharged for `2 ≤ n` and
positive coordinates.

## Radical-log positivity

The same module adds:

```text
Triple.log_rad_abc_pos
```

Positive `T.a,T.b` imply `2 ≤ T.a*T.b*T.c`; the existing
`log_rad_pos_of_two_le` then closes strict positivity.  Reduced public quality
bridges no longer request an explicit radical-log positivity hypothesis.

## Pure and affine support budgets

The following surfaces are available:

```text
GNSupportBudget
GNSupportBudgetAffine
GNSupportBudget.toAffine
Triple.GNValuationExcess_gt_of_quality_gt_affine
Triple.GNValuationExcess_gt_of_quality_gt_pred_affine
Triple.GNValuationExcess_gt_of_quality_gt_pred
```

The affine conclusion is:

```text
(((n-1)*(1+ε)-σ) * log(rad(a*b*c))) - C
  < GNValuationExcess n a b.
```

The `pred` versions internally use the unconditional return coefficient
`n-1`.  Their only global transport input is respectively an affine or pure
GN support budget.

No uniform support-budget theorem is asserted.  At this frontier:

```text
n may be fixed or varying;
σ may depend on n;
C may depend on n and ε;
the supplied budget is pointwise in T;
no theorem uniform over all positive ABC triples has been proved.
```

A useful budget must retain a positive net margin
`(n-1)*(1+ε)-σ`; existence of an arbitrary pointwise `σ` is insufficient.

## Exact high-lift carriers

`DkMath/ABC/GNHighLift.lean` adds:

```text
highLiftSupport
valuationExcess_eq_sum_highLift
GNValuationExcess_eq_sum_highLift
GNValuationExcess_eq_zero_of_no_highLift
```

The carrier is the factorization support filtered by `q^2 ∣ m`.  A support
prime outside this filter has factorization exponent exactly one, hence its
excess summand is zero.  Therefore the restriction is an exact equality, not
an estimate.  In particular, absence of GN prime-square carriers forces zero
GN valuation excess.

## Validation

```text
lake build DkMath.ABC.GNPowerLift
Build completed successfully (8262 jobs).

lake build DkMath.ABC.GNQualityExcessBridge
Build completed successfully (8338 jobs).

lake build DkMath.ABC.GNHighLift
Build completed successfully (8321 jobs).
```

No new `axiom`, `sorry`, or `native_decide` was added.  FLT7 modules and
shared aggregators were untouched.  No commit, push, PR, or CI action was
performed.  `#print axioms` on six representative new endpoints reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Next mathematical obligation

The single next obligation is a quantitatively useful affine
`GNSupportBudget`: with exact dependencies on fixed/varying `n`, `σ`, and
`C`, and with a positive net margin.  This checkpoint does not begin that
proof.
