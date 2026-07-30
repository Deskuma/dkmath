# FLT7-003 — Finite seven-axis power roll and nonzero thickness bound

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Current completed checkpoint:

```text
5c0e16f0 Add FLT7 seven-axis divisibility
```

## Objective

Iterate the one-layer `sevenAxis` peel a finite, explicitly bounded number of
times without defining a recursive depth function.

The checkpoint must formalize the exact equivalence

```text
sevenAxis ^ n ∣ x  ↔  7 ^ n ∣ norm x
```

and the exact norm scaling

```text
x = sevenAxis ^ n * y  →  norm x = 7 ^ n * norm y.
```

It must also expose the finite-thickness obstruction:

```text
x ≠ 0
sevenAxis ^ n ∣ x
→ 7 ^ n ≤ norm x.
```

Equivalently, a nonzero element whose norm is smaller than `7^n` cannot contain
`n` layers of the scale axis.

Do not define an unbounded `kappaDepth` or identify it with a valuation yet.

## New module

Create:

```text
DkMath/FLT/Seven/AxisPowerRoll.lean
```

Import:

```lean
import DkMath.FLT.Seven.AxisDivisibility
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenAxisPowerRoll.lean
```

Create the implementation report:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-003.md
```

## Required theorem surface

Names may be adjusted minimally to match local style, but preserve the theorem
content and report the final names.

### 1. Norm of an axis power

```lean
theorem norm_sevenAxis_pow (n : ℕ) :
    norm (sevenAxis ^ n) = (7 : ℤ) ^ n
```

Use `map_pow`-style reasoning only if an existing theorem fits naturally;
otherwise induct on `n` using `traceOne_norm_mul` and `sevenAxis_norm`.

### 2. Exact finite norm peel

```lean
theorem norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y) :
    norm x = (7 : ℤ) ^ n * norm y
```

This is the finite iteration of the FLT7-002 one-layer theorem.

### 3. Power divisibility equivalence

```lean
theorem sevenAxis_pow_dvd_iff_pow_seven_dvd_norm
    (n : ℕ) (x : TraceOneInt (-2)) :
    sevenAxis ^ n ∣ x ↔ (7 : ℤ) ^ n ∣ norm x
```

Prove this by induction on `n`.

Forward direction:

- unpack `x = sevenAxis^(n+1) * y`,
- use exact norm scaling.

Reverse direction for `n+1`:

1. derive `7 ∣ norm x` from `7^(n+1) ∣ norm x`,
2. use `sevenAxis_dvd_iff_seven_dvd_norm` to obtain `x = sevenAxis * y`,
3. use `norm x = 7 * norm y`,
4. cancel the nonzero integer factor `7` to obtain `7^n ∣ norm y`,
5. apply the induction hypothesis to `y`,
6. reassemble `sevenAxis^(n+1) ∣ x`.

Do not introduce ideals, associates, irreducibles, or a domain instance merely
to prove this theorem.

### 4. Nonzero quotient and positive shell

For an explicit factorization by a power, prove:

```lean
theorem ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y)
    (hx : x ≠ 0) :
    y ≠ 0
```

Then derive:

```lean
theorem one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y)
    (hx : x ≠ 0) :
    1 ≤ norm y
```

Reuse the positive-definite nonzero norm floor from FLT7-001.

### 5. Finite-thickness lower bound

Main geometric/arithmetic result:

```lean
theorem pow_seven_le_norm_of_sevenAxis_pow_dvd
    {x : TraceOneInt (-2)} {n : ℕ}
    (hx : x ≠ 0)
    (hdiv : sevenAxis ^ n ∣ x) :
    (7 : ℤ) ^ n ≤ norm x
```

Interpretation: each retained axis layer contributes one indivisible norm
thickness of `7`; a nonzero core cannot contain more layers than its norm can
pay for.

Also prove the immediate obstruction form:

```lean
theorem not_sevenAxis_pow_dvd_of_norm_lt_pow_seven
    {x : TraceOneInt (-2)} {n : ℕ}
    (hx : x ≠ 0)
    (hlt : norm x < (7 : ℤ) ^ n) :
    ¬ sevenAxis ^ n ∣ x
```

This theorem is the stable API expression of the fixed-thickness principle.

### 6. Strict finite descent

For positive `n`, prove that removing `n` layers strictly decreases norm:

```lean
theorem norm_lt_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hn : 0 < n)
    (hxy : x = sevenAxis ^ n * y)
    (hx : x ≠ 0) :
    norm y < norm x
```

Use exact scaling, `1 ≤ norm y`, and `2 ≤ 7^n` or an equivalent elementary
bound. Do not invoke logarithms or valuations.

## Optional theorem

Only if the required surface is complete and the proof is short, add:

```lean
theorem sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff
    (n : ℕ) (z y : ℤ) :
    sevenAxis ^ n ∣ cyclotomicSevenToTraceOne z y ↔
      (7 : ℤ) ^ n ∣ cyclotomicSeven z y
```

This should be a direct specialization of the generic power-divisibility
criterion and the existing cyclotomic norm identity.

Do not attempt to translate the right side into `7^n ∣ z-y`; that statement
requires additional hypotheses and is not part of this checkpoint.

## Tests

The focused test should cover at least:

- `n = 0`,
- `n = 1` recovering the FLT7-002 theorem,
- `x = sevenAxis ^ 2`, whose norm is `49`,
- a nonzero element with norm `< 49`, proving `sevenAxis ^ 2 ∤ x`,
- the optional cyclotomic specialization if implemented.

Avoid `native_decide`.

## Required report

Record:

- exact theorem surface,
- induction architecture for the reverse power-divisibility direction,
- how integer factor cancellation was handled,
- the finite-thickness lower bound and obstruction theorem,
- zero-element behavior,
- whether the optional cyclotomic specialization was included,
- recommended FLT7-004 boundary.

## Non-goals

Do not add:

- recursive or maximal `kappaDepth`,
- `padicValNat` equality,
- LTE,
- exact valuation of the cyclotomic kernel,
- `7^n ∣ cyclotomicSeven z y ↔ 7^n ∣ z-y`,
- coprime endpoint packets,
- FLT7 descent or a no-solution theorem,
- ideals, PID, UFD, Euclidean, or class-number theory,
- general odd-prime abstractions.

## Outcome classification

- Outcome A: finite power divisibility, exact norm scaling, finite-thickness
  lower bound, obstruction, and strict finite descent are complete.
- Outcome B: exact power divisibility and norm scaling are complete, but one
  order-theoretic thickness theorem needs a clearly identified follow-up.
- Outcome C: the proposed power equivalence fails; report a concrete
  counterexample or the exact cancellation obstruction.

Commit with a focused message and push to the current feature branch.
