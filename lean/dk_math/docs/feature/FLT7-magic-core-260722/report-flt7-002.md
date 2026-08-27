# FLT7-002 implementation report

## Outcome

Outcome A.  The generic one-layer seven-axis criterion, exact norm peel,
cyclotomic specialization, and natural `GN 7` endpoint-gap criterion are all
implemented.

## Files changed

- `DkMath/FLT/Seven/AxisDivisibility.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenAxisDivisibility.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-002.md`

## Exact theorem surface

Axis coordinates and generic divisibility:

- `sevenAxis_mul_fst`
- `sevenAxis_mul_snd`
- `sevenAxis_dvd_iff_seven_dvd_trace`
- `seven_dvd_norm_iff_seven_dvd_trace`
- `sevenAxis_dvd_iff_seven_dvd_norm`

One-layer norm peel:

- `norm_eq_seven_mul_norm_of_eq_sevenAxis_mul`
- `ne_zero_of_eq_sevenAxis_mul_of_ne_zero`
- `one_le_norm_of_eq_sevenAxis_mul_of_ne_zero`
- `norm_lt_of_eq_sevenAxis_mul_of_ne_zero`

Cyclotomic and GN specialization:

- `trace_cyclotomicSevenToTraceOne`
- `sevenAxis_dvd_cyclotomicSevenToTraceOne_iff`
- `seven_dvd_cyclotomicSeven_iff`
- `seven_dvd_GN_seven_sub_iff`

No proposed theorem was omitted.

## Explicit reverse witness

Writing `x=⟨a,b⟩` and `trace x=7*k`, the reverse implication in
`sevenAxis_dvd_iff_seven_dvd_trace` uses exactly

```text
⟨4*k-a, -k⟩.
```

Multiplication by `sevenAxis=(-1,2)` sends `⟨c,d⟩` to
`⟨-c-4d, 2c+d⟩`.  Substitution of this witness returns `⟨a,b⟩`; no integer
division is used.

## Exact one-layer norm peel

If `x=sevenAxis*y`, multiplicativity and `norm sevenAxis=7` give

```text
norm x = 7 * norm y.
```

When `x≠0`, the explicit equality directly rules out `y=0`, without adding an
integral-domain instance.  The FLT7-001 positive norm floor then gives
`1≤norm y`, hence `norm y<norm x`.

## Cyclotomic endpoint-gap criterion

The exact trace factorization is

```text
trace (cyclotomicSevenToTraceOne z y)
  = (z-y) * (2*(z-y)^2 + 7*z*y).
```

Primality of `7`, together with `7∤2`, reduces divisibility of the second
factor to divisibility of `(z-y)^2`, and therefore of `z-y`.  Consequently:

```text
sevenAxis ∣ cyclotomicSevenToTraceOne z y ↔ 7 ∣ z-y
7 ∣ cyclotomicSeven z y                  ↔ 7 ∣ z-y.
```

## GN7 criterion

For naturals with `b≤a`, the existing bridge uses gap `a-b`, base `b`, and
endpoint pair `(a,b)`.  Casting its norm identity to integers and applying the
cyclotomic criterion proves

```text
7 ∣ GN 7 (a-b) b ↔ 7 ∣ a-b.
```

Generic `GN` was not re-expanded.

## Scope preserved

No recursive kappa depth, higher valuation, LTE, power of `sevenAxis`, FLT7
counterexample packet, descent, ideal/factorization theory, or general
odd-prime abstraction was introduced.

## Verification and axiom audit

Focused builds, the Lean test file, forbidden-token scan, and
`git diff --check` are run at checkpoint close.  The exact `#print axioms`
sets are:

- `norm_eq_seven_mul_norm_of_eq_sevenAxis_mul`: `propext`, `Quot.sound`
- every other audited summit theorem: `propext`, `Classical.choice`,
  `Quot.sound`

No `sorryAx` or DkMath-defined axiom appears, and the implementation/test use
no active `native_decide`, `admit`, or `sorry`.

## Recommended FLT7-003 boundary

Define a finite, explicitly bounded iteration of the one-layer peel, or first
design the relation between repeated `sevenAxis` factors and `7`-adic norm
depth.  Keep recursive depth and valuation equality out of the stable API until
termination and zero-element conventions are fixed explicitly.
