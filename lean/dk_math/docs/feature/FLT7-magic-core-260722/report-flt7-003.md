# FLT7-003 implementation report

## Outcome

Outcome A.  Finite axis-power divisibility, exact norm scaling, the nonzero
thickness bound and obstruction, strict finite descent, and the optional
cyclotomic specialization are complete.

## Files changed

- `DkMath/FLT/Seven/AxisPowerRoll.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenAxisPowerRoll.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-003.md`

## Exact theorem surface

- `norm_sevenAxis_pow`
- `norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul`
- `sevenAxis_pow_dvd_iff_pow_seven_dvd_norm`
- `ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero`
- `one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero`
- `pow_seven_le_norm_of_sevenAxis_pow_dvd`
- `not_sevenAxis_pow_dvd_of_norm_lt_pow_seven`
- `norm_lt_of_eq_sevenAxis_pow_mul_of_ne_zero`
- `sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff`

## Induction and cancellation architecture

The forward power-divisibility implication unpacks an explicit factorization
and applies exact norm scaling directly.

For the reverse successor step, `7^(n+1) ∣ norm x` first supplies
`7 ∣ norm x`.  FLT7-002 gives an explicit factorization `x=sevenAxis*y` and
the exact equality `norm x=7*norm y`.  Comparing this equality with the
original power-divisibility witness yields an equality with common left factor
`7`.  The proof cancels that factor using `mul_left_cancel₀` and the concrete
fact `(7:ℤ)≠0`, obtaining `7^n ∣ norm y`.  The induction hypothesis supplies
`sevenAxis^n ∣ y`, and associativity/power arithmetic reconstructs the
successor factorization.  No domain instance or ideal theory is introduced.

## Finite thickness and strict descent

For an explicit factorization `x=sevenAxis^n*y`, norm multiplicativity gives

```text
norm x = 7^n * norm y.
```

If `x≠0`, then `y≠0` follows directly because `y=0` would make the displayed
factorization equal to zero.  The positive-definite floor gives `1≤norm y`, so

```text
7^n ≤ norm x.
```

The stable contrapositive API states that `norm x<7^n` forbids
`sevenAxis^n ∣ x`.  For `0<n`, the elementary bound `2≤7^n` makes the exact
scaling strict: `norm y<norm x`.

## Zero-element behavior

The divisibility equivalence itself includes zero: every finite axis power
divides zero, and every `7^n` divides `norm 0=0`.  Nonzero hypotheses appear
only where a positive quotient shell, thickness lower bound, obstruction, or
strict norm decrease is claimed.

## Cyclotomic specialization

The optional theorem is included.  It specializes the generic equivalence and
rewrites the existing identity
`cyclotomicSeven z y = norm (cyclotomicSevenToTraceOne z y)`.  It deliberately
does not claim `7^n ∣ cyclotomicSeven z y ↔ 7^n ∣ z-y`.

## Scope preserved

No maximal/recursive kappa depth, valuation equality, LTE, exact cyclotomic
valuation, endpoint packet, FLT7 descent, ideal/factorization theory, or
general odd-prime abstraction was added.

## Verification and axiom audit

Focused builds, tests, forbidden-token scan, and `git diff --check` are run at
checkpoint close.  Every audited theorem above has the exact standard axiom
set `propext`, `Classical.choice`, and `Quot.sound`.  No `sorryAx` or
DkMath-defined axiom appears, and the implementation/test use no active
`native_decide`, `admit`, or `sorry`.

## Recommended FLT7-004 boundary

Design the zero convention and finiteness witness for a maximal axis-depth API,
then relate that bounded depth to an integer or natural `7`-adic valuation.
Keep the first implementation finite/bounded until the maximality and
termination interface is fixed.
