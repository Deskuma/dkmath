# Report 006: finite exceptional absorption and lifted-radical return

## Outcome

Outcome A is complete in:

```text
DkMath/ABC/GNSupportReturn.lean
```

## Exact support definitions and partition

The module defines:

```text
GNExceptionalSupport
GNNonExceptionalSupport
GNExceptionalSupportProduct
GNNonExceptionalSupportProduct
```

and proves:

```text
GN_support_eq_exceptional_union_nonExceptional
GNExceptionalSupport_disjoint_nonExceptional
rad_GN_eq_exceptional_mul_nonExceptional
```

Thus GN factorization support is an exact disjoint filtered partition, and
its radical is exactly the product of the two squarefree support products.

## Exceptional absorption

```text
GNExceptionalSupportProduct_dvd_rad
log_GNExceptionalSupportProduct_le_log_rad
log_rad_GN_le_log_rad_exp_add_log_nonExceptional
```

Every exceptional member is a prime factorization-support member satisfying
`q ∣ n`.  The existing
`prime_channel_family_prod_dvd_supportMass` theorem sends their finite product
into `supportMass n`, and `supportMass_eq_abc_rad` identifies this with
`rad n`.  Consequently:

```text
log(rad GN) ≤ log(rad n) + log(nonExceptionalProduct).
```

## Freshness

```text
Triple.nonExceptionalSupport_fresh
```

For `1 ≤ n`, `0 < T.a`, and `q` in non-exceptional GN support, it proves:

```text
Prime q
q ∣ GN
q ∤ T.a
q ∤ T.b
q ∤ T.c
q ∤ T.a*T.b*T.c
```

Boundary freshness uses the exponent-exception theorem.  Freshness from
`T.b` and `T.c` uses coprimality of the GN power lift: `q ∣ GN` places `q`
in the lifted left coordinate, while divisibility of `b` or `c` would place
it in the corresponding powered coordinate.

## Lifted radical bridge

```text
Triple.rad_mul_nonExceptionalProduct_dvd_lift_rad
Triple.log_rad_add_log_nonExceptional_le_log_lift_rad
```

For `2 ≤ n` and positive `T.a,T.b`:

```text
rad(a*b*c) * nonExceptionalProduct
  ∣ rad(lift.a * lift.b * lift.c).
```

The proof forms the disjoint union of original ABC prime support and fresh
non-exceptional GN support.  Every union member is a prime channel of the
lifted coordinate product, so the finite prime-family support-mass theorem
gives the divisibility.  No false `rad(GN) ≤ rad(abc)` transport is used.

## Exact affine transport

The module defines:

```text
GNLiftRadicalGrowthBudgetAffine
GNNonExceptionalSupportBudgetAffine
```

and proves the deterministic chain:

```text
Triple.nonExceptionalSupportBudgetAffine_of_liftGrowth
Triple.GNSupportBudgetAffine_of_nonExceptional
Triple.GNSupportBudgetAffine_of_liftGrowth
```

The constants transport exactly as:

```text
lift growth budget (σ,C)
  -> non-exceptional budget (σ,C)
  -> full GN support budget (σ, C + log(rad n)).
```

Finally:

```text
Triple.GNValuationExcess_gt_of_quality_gt_liftGrowth
```

proves the excess lower bound

```text
(((n-1)*(1+ε)-σ) * log(rad(a*b*c)))
  - (C + log(rad n))
  < GNValuationExcess n a b
```

from high quality and the lifted-radical-growth budget alone.

## Remaining global obligation

The remaining input is a quantitatively useful, genuinely uniform
`GNLiftRadicalGrowthBudgetAffine` (or equivalently a non-exceptional support
growth bound) with a positive net margin.  No such uniform theorem, high-lift
rarity result, `K_ε`, or ABC conclusion is claimed here.

## Validation and scope

```text
lake build DkMath.ABC.GNSupportReturn
Build completed successfully (8342 jobs).
```

No new `axiom`, `sorry`, or `native_decide` was added.  The direct import
`DkMath.ABC.GNSupportReturn` is sufficient; no shared aggregator was changed.
`#print axioms` on six representative endpoints reports only `propext`,
`Classical.choice`, and `Quot.sound`.
FLT7 modules and documentation were untouched.  No commit, push, PR, or CI
operation was performed.
