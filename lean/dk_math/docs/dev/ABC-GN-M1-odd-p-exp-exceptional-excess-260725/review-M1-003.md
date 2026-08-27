# M1-003 Review: exponent-five exceptional excess zero

Reviewed commit: `8a9690b41be321fed2b15dc9d578512388322a0d`

## Decision

**Fully accepted.**

```text
critical issues: 0
major issues:    0
required fixes:  0
```

M1-003 completes the fixed-exponent-five minimum victory:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

Hence the exceptional valuation budget at exponent five is exactly:

```text
τe = 0
De = 0
```

## 1. Finite-sum proof

The proof unfolds only `GNExceptionalValuationExcess` and eliminates every summand in the filtered factorization support.

For an index `q` in the filtered support it obtains:

```text
q ∈ (GN 5 T.a T.b).factorization.support
q ∣ 5
```

The support witness gives primality through:

```lean
Nat.support_factorization
Nat.prime_of_mem_primeFactors
```

Since both `q` and `5` are prime and `q ∣ 5`, the proof correctly derives:

```text
q = 5
```

using `Nat.prime_dvd_prime_iff_eq`.

After `subst q`, the original outer-context support witness remains available. It is converted canonically to:

```lean
5 ∣ GN 5 T.a T.b
```

via:

```lean
Finsupp.mem_support_iff
Nat.dvd_of_factorization_pos
```

The M1-002 endpoint then rewrites the multiplicity to one:

```lean
factorization_five_GN_five_eq_one_of_dvd T.hcop h5GN
```

Therefore the summand is exactly:

```text
((1 - 1 : ℕ) : ℝ) * Real.log (5 : ℝ) = 0
```

and `Finset.sum_eq_zero` closes the full exceptional sum.

No modulo-five or modulo-twenty-five arithmetic is duplicated.

## 2. Positivity assumptions

The stronger theorem surface without positivity assumptions is correct.

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0
```

The proof needs only:

```text
T.hcop
factorization support membership
prime divisibility of 5
```

The endpoint also covers the valid boundary triples with a zero coordinate, for example the structural cases represented by `(0,1,1)` or `(1,0,1)`.

## 3. Exact affine budget

`GNExceptionalExcessBudgetAffine` is defined by:

```text
GNExceptionalValuationExcess n T.a T.b
  ≤ τ * log(rad(T.a*T.b*T.c)) + D
```

Substitution of the finite-sum theorem with `τ = 0` and `D = 0` leaves `0 ≤ 0`, so the wrapper is exact rather than merely bounded by a positive constant.

This is the correct endpoint for insertion into `ABCGNFinalBudgetContract`.

## 4. Dependency review

The placement is correct:

```text
GNOddPrimeExceptionalExcess
  -> GNExceptionalExcessFive
  <- GNFinalBudgetBridge
```

The low-dependency local arithmetic kernel from M1-002 remains unchanged. The finite-sum and final-budget bridge are isolated in the new thin module.

There is no dependency on `DkMath.FLT.Five.*`, no aggregator modification, and no unrelated refactor.

## 5. Trust boundary

The report records:

```text
focused build: success
new sorry:      none
new axiom:      none
native_decide:  none
```

The endpoint axiom audit contains only:

```text
propext
Classical.choice
Quot.sound
```

No new DkMath project axiom enters the proof.

## 6. Mathematical meaning

At exponent five, every exponent-exceptional support prime is the unique channel `5`, and that channel occurs with multiplicity exactly one whenever it occurs at all.

Therefore `rad` loses no multiplicity on the exponent-exceptional side:

```text
exceptional support width: at most one channel
exceptional depth:         exactly one copy
exceptional excess:        zero
```

For the fixed `n = 5` ABC-GN route, the final three-budget margin has now reduced from:

```text
support + exceptional depth + non-exceptional depth
```

to:

```text
support + non-exceptional depth
```

This is a genuine mathematical reduction, not only an API wrapper.

## 7. Checkpoint boundary

M1-003 correctly stops before:

```text
M1-004 odd-prime local generalization
M1-005 odd-prime finite-sum and budget closure
M2 support-growth work
M3 non-exceptional high-lift work
aggregator changes
```

## Final verdict

```text
M1-000  complete
M1-001  complete / Outcome B
M1-002  complete
M1-003  complete / fixed-five minimum victory
M1-004  next
```

**M1-003 is accepted without modification.**
