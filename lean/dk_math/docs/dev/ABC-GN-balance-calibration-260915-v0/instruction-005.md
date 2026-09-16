# instruction-005 — Exceptional cubic gauge completion

## 0. Purpose

BCAL-004 established the exact generic non-exceptional shell identity

```text
GNChannelBalance
  = log(nonExceptionalSingleLayer)
    - log(twoTail(nonExceptionalPart)).
```

For the cubic specialization `p = 3`, the existing full cubic complement may additionally contain the exceptional prime `3` at valuation exactly one.  Therefore BCAL-004 correctly stopped at Outcome B rather than identifying the full complement unconditionally with the BCAL single layer.

BCAL-005 must recover that missing information explicitly instead of excluding it by hypothesis.

The target is an unconditional exact cubic-shell bridge in which the discrepancy is exactly the exceptional-support / gauge coordinate already introduced in BCAL-002.

No estimate, uniform bound, Hensel transport, or ABC closure is part of this checkpoint.

---

## 1. Authoritative existing API

Read and reuse, at minimum:

```text
DkMath/ABC/GNBalanceCubicShell.lean
DkMath/ABC/ABCCalibrationSourceDecomposition.lean
DkMath/ABC/GNSupportReturn.lean
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

Important existing facts include:

```text
GNChannelBalance_eq_log_singleLayer_sub_log_twoTail
GN_cubic_three_factorization_eq_one_of_dvd
GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart
GNExceptionalSupportProduct
GNExceptionalGaugeSlack
GNExceptionalSupportProduct_dvd_rad
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
not_nine_dvd_GN_three_one_value
```

Do not duplicate these definitions.

---

## 2. Exact arithmetic picture to verify

For

```text
F(a) = GN 3 a 1 = a^2 + 3*a + 3,
```

prime `3` satisfies

```text
v₃(F(a)) = 0 or 1,
```

never `>= 2`.

Thus `3` never contributes to the repeated part or `twoTail`, but when present it remains in the full squarefree cubic complement.

The BCAL channel, however, is defined from the non-exceptional support and therefore omits primes dividing the exponent `p = 3`.

Hence the missing full-shell information should be exactly the exceptional single-layer factor.

The first preferred target is the multiplicative identity

```text
GNExcessCubicComplement a
  = GNExceptionalSupportProduct 3 a 1
    * GNNonExceptionalSingleLayer 3 a 1
```

or an equivalent orientation accepted by Lean.

Do not assume this identity merely from names.  Prove it from factorization/support/repeated-part theorems.

If a cleaner exact theorem already exists under another name, reuse it rather than adding a duplicate.

---

## 3. Exceptional product specialization

If useful and not already available, expose the exact cubic exceptional product:

```text
GNExceptionalSupportProduct 3 a 1
  = if 3 ∣ GN 3 a 1 then 3 else 1
```

or equivalent paired theorems for the two cases.

This theorem should follow from:

- exceptional support means support primes dividing `3`;
- such a prime must be `3`;
- `v₃(F(a)) <= 1`.

No stronger divisibility statement is requested.

---

## 4. twoTail compatibility

Verify explicitly whether

```text
twoTail (GN 3 a 1)
  = twoTail (GNNonExceptionalPart 3 a 1)
```

holds unconditionally.

It is expected because the only omitted exceptional prime is `3`, and its valuation is at most one, so it contributes exponent zero to `twoTail`.

Again, prove this from the current factorization API.  If an existing theorem already gives the required rewrite, use it.

If exact equality unexpectedly fails because of a definition-level issue, stop that subgoal and report the precise mismatch rather than forcing a rewrite.

---

## 5. Unconditional full cubic shell bridge

Using the results above, target an unconditional theorem of the form

```text
GNChannelBalance (Triple.mk a 1 (a + 1) ...) 3
  = log(GNExcessCubicComplement a)
    - log(twoTail (GN 3 a 1))
    - log(GNExceptionalSupportProduct 3 a 1)
```

up to harmless reassociation / orientation of subtraction.

This is the central BCAL-005 theorem.

Conceptually:

```text
full cubic shell balance
  = BCAL non-exceptional balance
    + exceptional single-layer log mass.
```

Equivalently,

```text
BCAL balance
  = full cubic shell balance
    - exceptional single-layer log mass.
```

No inequality is desired here.

---

## 6. Gauge-slack rewrite

BCAL-002 defined

```text
GNExceptionalGaugeSlack T p
  = log(rad p)
    - log(GNExceptionalSupportProduct p T.a T.b).
```

For the cubic triple and `p = 3`, rewrite the unconditional shell bridge through this existing gauge coordinate.

A preferred theorem shape is conceptually

```text
GNChannelBalance
  = fullCubicShellBalance
    - log(rad 3)
    + GNExceptionalGaugeSlack T 3.
```

Because `rad 3 = 3`, a specialized `log 3` form is acceptable if it is more natural in Lean, but prefer reuse of `rad` / gauge APIs where practical.

This theorem is important: it should show that the obstruction encountered in BCAL-004 is not a new error term.  It is exactly the already-known exceptional gauge coordinate from BCAL-002.

Avoid creating a new independent "cubic correction" definition unless there is a clear API reason.

---

## 7. Recover the BCAL-004 conditional theorem

The existing theorem

```text
GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail
```

uses the hypothesis

```text
¬ 3 ∣ GN 3 a 1.
```

After the unconditional exceptional bridge is available, prove or refactor a corollary showing that this old conditional theorem is recovered when the exceptional product is `1`.

Do not delete or break the existing theorem unless a strict API improvement is obvious and all callers are updated safely.

Optional second specialization:

when

```text
3 ∣ GN 3 a 1,
```

record the complementary exact formula in which the full cubic shell differs from BCAL balance by `log 3` and the exceptional gauge slack is zero, if this is straightforward from the new API.

This is useful but not mandatory if it causes disproportionate proof engineering.

---

## 8. Relation to exact calibration correction

Audit whether the same term

```text
log(GNExceptionalSupportProduct 3 a 1)
```

can be used to rewrite the cubic specialization of `GNExactCalibrationCorrection` without introducing new assumptions.

A small exact corollary is welcome if it directly reuses existing theorems.

Do NOT enlarge this checkpoint into a new epsilon proof or a new ABC contract.

The intended structural observation is only:

```text
exceptional support log
```

is simultaneously

1. the information missing from the BCAL-004 full cubic shell bridge; and
2. the exact exceptional term already present inside BCAL-002 calibration accounting.

If an exact Lean bridge is awkward or would duplicate existing formulas, record this observation only in the report.

---

## 9. Suggested production module

Preferred location:

```text
DkMath/ABC/GNBalanceCubicExceptionalGauge.lean
```

Alternative placement is acceptable if the existing hierarchy strongly suggests another module.

Export through:

```text
DkMath/ABC.lean
```

only for reusable production theorems.

---

## 10. Explicit non-goals

Do not prove or assume:

- a uniform calibration bound;
- a supremum bound;
- a numerical exponent improvement;
- a new ABC contract;
- ABC itself;
- Hensel lifting or valuation mutation;
- global monotonicity of `GNChannelBalance`;
- optimality of the pivot;
- shell counting / dyadic incidence bounds;
- PowerSwap abstraction;
- any new axiom.

This is an exact bookkeeping / transport checkpoint only.

---

## 11. Outcome classes

### Outcome A — EXACT EXCEPTIONAL COMPLETION

Preferred outcome.  Obtain an unconditional full cubic shell bridge with the exceptional-support correction, plus its gauge-slack rewrite.

### Outcome B — PARTIAL EXCEPTIONAL COMPLETION

Obtain exact exceptional-product / complement / twoTail relations but not the final logarithmic identity.  Record the precise remaining API obstacle.

### Outcome C — AUDIT ONLY

If the existing abstractions have discarded information needed for the bridge, add no forced theorem.  Report exactly what information is unavailable and where.

---

## 12. Validation

Run at minimum:

```text
focused module build
lake build DkMath.ABC
git diff --check
forbidden-token scan
#print axioms on central bridge theorem(s)
```

No `sorryAx`; expected logical axioms should remain within the existing production baseline.

---

## 13. Report

Write:

```text
docs/dev/ABC-GN-balance-calibration-260915-v0/report-005.md
```

Include:

- Outcome A/B/C;
- exact exceptional support product behavior for `p=3`;
- whether full complement factors as exceptional-single × nonexceptional-single;
- whether full/nonexceptional `twoTail` agree;
- unconditional shell-balance theorem, if obtained;
- gauge-slack rewrite, if obtained;
- relationship to BCAL-002 exact correction;
- whether BCAL-004 Outcome B is now fully explained/closed;
- whether Hensel/depth transport is justified as the next checkpoint.

The governing principle is:

> Do not hide the exceptional prime by a side condition.  Make its exact contribution a coordinate.
