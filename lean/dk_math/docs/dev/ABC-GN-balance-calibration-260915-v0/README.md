# ABC–GN Balance / Calibration Research

Branch: `research/ABC-GN-balance-calibration-260915-v0`

Base: `develop` at `5bba76f07a966e23eba7d0fbf7c70f1133d7e90e`

## 1. Purpose

This branch changes the research question.

The immediate goal is **not** to improve a numerical exponent such as `0.435`, a shell-count exponent, or a square-full counting exponent. Those numbers are outputs of particular estimates.

The goal is to expose the underlying **balance law** already present in the production ABC formalization:

- what is the total load,
- what are the two exchangeable components,
- where is the balance point,
- what is the signed imbalance coordinate,
- which term is a genuine structural defect,
- which term is only a finite-scale calibration correction,
- how the final `Kε` packages that calibration into the classical ABC statement.

The conceptual model is the same one used by `DkMath.PowerSwap`: first define the exact two-sided coordinate system and the zero-contour, then study estimates as measurements of that geometry.

No theorem on this branch may claim that ABC is proved unless it is already a consequence of the existing production API.

## 2. Existing exact outer balance

Production already contains an exact ABC imbalance coordinate.

For a positive `Triple T`, the implemented theorem

```lean
Triple.abcGap_eq_valuationExcess_sub_log_rad_ab
```

identifies

```text
abcGap(T)
  = valuationExcess(T.c)
    - log(rad(T.a * T.b)).
```

The normalized intrinsic coordinate is already defined by

```lean
Triple.abcEpsilon
```

and production proves

```lean
Triple.abcGap_eq_abcEpsilon_mul_radLog
Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc
Triple.quality_eq_one_add_abcEpsilon
```

Hence the outer balance point is exactly

```text
abcGap(T) = 0
```

or equivalently

```text
quality(T) = 1
abcEpsilon(T) = 0.
```

This branch treats this as the **outer balance contour**. The external epsilon of the classical ABC statement is not the balance point; it is an allowed slope away from the balance contour.

## 3. Existing exact GN accounting

For an odd prime exponent `p`, production already splits the GN logarithmic mass into exceptional support, fresh non-exceptional support, and non-exceptional valuation depth.

The central existing quantities are:

```lean
GNExceptionalSupportProduct
GNNonExceptionalSupportProduct
GNNonExceptionalValuationExcess
```

and production contains exact accounting theorems including

```lean
Triple.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
```

The current joint channel budget is

```lean
GNNonExceptionalChannelMassBudgetAffine
```

whose mathematical content is

```text
S + E <= ρ * R + C
```

where

```text
R := log(rad(a*b*c))
S := log(GNNonExceptionalSupportProduct p a b)
E := GNNonExceptionalValuationExcess p a b.
```

Production already proves

```lean
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
```

so the lifted-radical joint-pressure formulation and the direct fresh-support-plus-depth formulation are exactly equivalent.

## 4. Missing coordinate: balance, not mass

The current production route uses only

```text
M := S + E
```

because an upper bound for total channel mass is enough for the deterministic reduction to ABC.

For balance analysis this loses information. Introduce also

```text
Q := S - E.
```

Interpretation:

```text
Q > 0   fresh-support dominated
Q = 0   support/depth balance contour
Q < 0   repeated-depth dominated
```

Then

```text
S = (M + Q) / 2
E = (M - Q) / 2.
```

The first implementation checkpoint should formalize these identities only. It must not assert that `Q = 0` is globally preferred, stable, attainable, or sufficient for ABC.

## 5. Calibration residual

The affine joint budget suggests a canonical signed residual:

```text
Cal(T,p,ρ) := S + E - ρ * R.
```

Then the existing budget

```text
S + E <= ρ * R + C
```

is exactly

```text
Cal(T,p,ρ) <= C.
```

This gives a precise meaning to the existing constant field `C`:

> `C` is a uniform upper calibration allowance for the signed channel residual at the selected slope `ρ`.

The first branch goal is to make this residual an explicit mathematical object and prove only equivalences that follow algebraically from existing production theorems.

Do **not** define `C` itself as the residual. Pointwise residual and uniform calibration allowance are different objects.

## 6. Relation to intrinsic ABC epsilon

Production already defines

```lean
GNEpsilon p ρ := ρ / (p - 1) - 1
```

and proves

```lean
GNEpsilon_le_iff_margin
Triple.abcEpsilon_le_GNEpsilon_add_correction
```

The correction term has the exact shape

```text
(C + log(rad p)) / ((p - 1) * radLog(T)).
```

Thus the current deterministic bridge already separates:

1. slope calibration: `GNEpsilon p ρ`,
2. affine residual allowance: `C`,
3. fixed exponent gauge correction: `log(rad p)`,
4. scale normalization: division by `(p - 1) * radLog(T)`.

The later classical multiplicative constant is produced through

```lean
GNABCConstant
```

and is a safe positive envelope for the additive logarithmic correction. It should be treated as the **outer calibration display**, not as the primitive balance quantity.

## 7. Research questions after the thin API exists

Only after the exact coordinate API is kernel-checked should later checkpoints investigate:

1. Which existing exact decompositions further split `Cal` into structural terms?
2. How does `Q = S - E` transform under Hensel depth growth, fresh-prime return, orientation change, and cubic shell transport?
3. Is there a natural invariant or monotone quantity involving both `M` and `Q`?
4. Which previously observed numerical exponents are slopes/supporting lines of the same balance region?
5. Which part of `C` is unavoidable arithmetic calibration, and which part is proof-envelope slack?
6. Can shell coordinates `(repeated part, squarefree complement)` be linked by an exact map to the GN support/depth balance coordinates?

These are research questions, not current claims.

## 8. Stop conditions

Stop and report rather than forcing a theorem if any of the following occurs:

- the proposed `balance` coordinate reduces to a pure rename with no useful consumer;
- an identity requires a new arithmetic hypothesis not present in production;
- a proposed exact equality is only an inequality in existing code;
- extracting `Cal` silently assumes the uniform contract that is equivalent in strength to ABC;
- a new theorem would merely restate `ABCGNOddPrimeJointContract` under different notation.

The value of this branch is in exposing the scale/balance/calibration geometry without hiding the remaining arithmetic frontier.
