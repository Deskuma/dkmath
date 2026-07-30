# FLT7-002 — Seven-axis divisibility and exact norm peel

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

The working tree is clean and FLT7-001 is complete at commit:

```text
783a2002 Add FLT7 quadratic magic core
```

## Objective

Formalize one exact layer of the discriminant `-7` scale axis.

Do not define a recursive kappa-depth yet. Do not start an FLT7 descent.

The checkpoint must prove that divisibility by `sevenAxis` is equivalent to
divisibility of the trace and norm by `7`, and then specialize this result to
the seventh cyclotomic kernel and the existing `GN 7` bridge.

## New module

Create:

```text
DkMath/FLT/Seven/AxisDivisibility.lean
```

Import only the existing FLT7 quadratic bridge unless a strictly lower import
is sufficient.

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests in:

```text
DkMathTest/FLT/SevenAxisDivisibility.lean
```

## Mathematical core

For `x = ⟨a,b⟩ : TraceOneInt (-2)` and
`sevenAxis = ⟨-1,2⟩`, multiplication is

```text
sevenAxis * ⟨c,d⟩ = ⟨-c - 4*d, 2*c + d⟩.
```

Prove coordinate lemmas for this multiplication.

The first summit theorem is:

```lean
theorem sevenAxis_dvd_iff_seven_dvd_trace
    (x : TraceOneInt (-2)) :
    sevenAxis ∣ x ↔ (7 : ℤ) ∣ trace x
```

Do not use integer division to construct the reverse witness.

If

```text
trace x = 7*k
```

for `x = ⟨a,b⟩`, use the explicit witness

```text
⟨4*k - a, -k⟩
```

and verify by extensionality and ring arithmetic.

Next prove:

```lean
theorem seven_dvd_norm_iff_seven_dvd_trace
    (x : TraceOneInt (-2)) :
    (7 : ℤ) ∣ norm x ↔ (7 : ℤ) ∣ trace x
```

Use the existing completed-square identity

```text
4 * norm x = trace x ^ 2 + 7 * x.snd ^ 2
```

and the primality of `7`.

Then combine them:

```lean
theorem sevenAxis_dvd_iff_seven_dvd_norm
    (x : TraceOneInt (-2)) :
    sevenAxis ∣ x ↔ (7 : ℤ) ∣ norm x
```

## Exact norm peel

Prove that an explicit axis factor removes exactly one factor of `7` from the
norm:

```lean
theorem norm_eq_seven_mul_norm_of_eq_sevenAxis_mul
    {x y : TraceOneInt (-2)}
    (hxy : x = sevenAxis * y) :
    norm x = 7 * norm y
```

Use only `traceOne_norm_mul` and `sevenAxis_norm`.

For nonzero `x`, derive that `y` is nonzero and prove:

```text
1 ≤ norm y
norm y < norm x
```

Use the positive-definite nonzero norm floor from FLT7-001.

Do not assume or add an integral-domain instance merely for this step:
`y = 0` would directly imply `x = 0` from the explicit equality.

## Cyclotomic specialization

Prove the exact trace factorization:

```text
trace (cyclotomicSevenToTraceOne z y)
  = (z - y) * (2 * (z - y)^2 + 7 * z * y)
```

An equivalent expanded identity is acceptable as an auxiliary lemma.

Then prove:

```lean
theorem sevenAxis_dvd_cyclotomicSevenToTraceOne_iff
    (z y : ℤ) :
    sevenAxis ∣ cyclotomicSevenToTraceOne z y ↔
      (7 : ℤ) ∣ z - y
```

The nontrivial direction should reduce modulo `7` to divisibility of

```text
2 * (z - y)^3
```

and use primality of `7` together with `7 ∤ 2`.

Using the existing norm identity, prove:

```lean
theorem seven_dvd_cyclotomicSeven_iff
    (z y : ℤ) :
    (7 : ℤ) ∣ cyclotomicSeven z y ↔
      (7 : ℤ) ∣ z - y
```

Finally add the natural-number GN endpoint-gap form:

```lean
theorem seven_dvd_GN_seven_sub_iff
    (a b : ℕ) (hab : b ≤ a) :
    7 ∣ GN 7 (a - b) b ↔ 7 ∣ a - b
```

Reuse `GN_seven_sub_eq_traceOneNorm_negTwo`; do not re-expand generic `GN`
unless coercion handling makes a short local calculation clearly preferable.

## Required report

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-002.md
```

Record:

- exact theorem surface,
- the explicit reverse divisibility witness,
- the one-layer norm peel,
- the cyclotomic endpoint-gap criterion,
- the GN7 criterion,
- any theorem omitted because an existing mathlib API made the proposed shape
  awkward,
- recommended boundary for FLT7-003.

## Non-goals

Do not add:

- recursive `kappaDepth`,
- equality with `padicValNat`,
- LTE,
- exact higher valuations,
- powers of `sevenAxis`,
- an FLT7 counterexample structure,
- an FLT7 theorem or descent,
- ideal, PID, UFD, Euclidean, or class-number theory,
- a general odd-prime abstraction.

## Outcome classification

- Outcome A: all one-layer axis, norm, cyclotomic, and GN theorems are complete.
- Outcome B: generic axis/norm peel is complete, but one specialization requires
  a clearly identified follow-up.
- Outcome C: the proposed divisibility equivalence is false or blocked by a
  concrete representation mismatch; report the exact counterexample or blocker.

Commit the completed checkpoint with a focused message and push to the current
feature branch.
