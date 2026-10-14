# GAGE-002 — Prime-power purity detector

Branch: `research/Exponent-Unit-Gauge-260923-v0`
Checkpoint: GAGE-002
Result: **Outcome A — implemented**

## 1. Outcome

The exponent gauge now has the reverse prime-power characterization for every
nontrivial row. If a prime `p` divides every interior coefficient of row `n`
and `1 < n`, then `n` is a positive power of that same `p`.

The implementation reuses the pinned Mathlib Lucas converse and does not
re-prove Lucas's theorem or Kummer carry theory. It also exposes the interior
Pascal gcd as a thin prime-power purity detector.

## 2. Exact pinned Mathlib declarations

The pinned Mathlib source is `Mathlib.Data.Nat.Choose.Lucas`. The exact
declarations used are:

```text
Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat
Choose.gcd_choose_eq_minFac_of_isPrimePow
Choose.gcd_choose_eq_one_of_not_isPrimePow
```

The reverse proof also uses the existing conversion lemma
`Nat.modEq_zero_iff_dvd`. The Mathlib theorem names are in the root `Choose`
namespace for this pinned version; `multiplicity` and `IsPrimePow` are
root-level declarations rather than `Nat.multiplicity` or `Nat.IsPrimePow`
names.

## 3. Reverse characterization proof path

Production theorem:

```text
innerRowSupportPrime_eq_prime_pow
  (hn : 1 < n)
  (h : InnerRowSupportPrime n p) :
  ∃ e, 0 < e ∧ n = p ^ e
```

The proof performs the following steps:

1. Extract `hp : p.Prime` and the all-interior divisibility predicate from
   `h`.
2. For every `i ∈ Finset.Icc 1 (n - 1)`, convert the divisibility statement
   into `Nat.choose n i ≡ 0 [MOD p]` using
   `Nat.modEq_zero_iff_dvd`.
3. Apply
   `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat` with the explicit
   `Fact p.Prime` argument to obtain
   `n = p ^ multiplicity p n`.
4. Use `1 < n` to rule out zero multiplicity, giving the required positive
   exponent witness.

The iff facade is also provided:

```text
innerRowSupportPrime_iff_prime_pow
  (hn : 1 < n) :
  InnerRowSupportPrime n p ↔
    p.Prime ∧ ∃ e, 0 < e ∧ n = p ^ e
```

Its reverse direction reuses `prime_power_innerRowSupportPrime`; no new row
support proof is duplicated.

## 4. Vacuous rows and boundary

The reverse theorem explicitly requires `1 < n`. This is necessary because the
interior-support predicate is vacuous for rows `n = 0` and `n = 1`; no
unconditional reverse characterization was added. Tests explicitly confirm
that `1 < 0` and `1 < 1` are false.

## 5. Public API added

In `DkMath.NumberTheory.Gauge.Exponent`:

```text
exponentGaugeInteriorGCD
innerRowSupportPrime_eq_prime_pow
innerRowSupportPrime_iff_prime_pow
exponentGaugeInteriorGCD_eq_minFac_of_isPrimePow
exponentGaugeInteriorGCD_eq_one_of_not_isPrimePow
```

The row-level quantity is definitionally thin:

```text
exponentGaugeInteriorGCD n := (Finset.Icc 1 (n - 1)).gcd n.choose
```

The two gcd theorems directly bridge to the pinned Mathlib results:

```text
IsPrimePow n       -> exponentGaugeInteriorGCD n = n.minFac
1 < n and not PP   -> exponentGaugeInteriorGCD n = 1
```

No additional iff was added because these two exact wrappers are already the
requested detector surface and avoid extra arithmetic unrelated to the
checkpoint.

## 6. Examples and calibrations

The focused test covers:

- row `3` as `3 ^ 1` through the reverse characterization;
- row `9` as a positive power of `3`;
- row `8` as a positive power of `2`;
- rows `6` and `12` with interior gcd `1` through the non-prime-power gcd
  theorem;
- rows `9` and `8` through the prime-power gcd theorem;
- the explicit `n = 0` and `n = 1` nontrivial-row boundary;
- the existing GAGE-001 height and support examples.

Small prime-power witnesses in the tests use theorem-driven
`isPrimePow_nat_iff` proofs; no general detector proof relies on numerical
calibration.

## 7. Files changed

```text
DkMath/NumberTheory/Gauge/Exponent.lean
DkMathTest/NumberTheory/Gauge/Exponent.lean
DkMathTest/NumberTheory/Gauge/ExponentAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-002.md
```

The public `DkMath.NumberTheory.Gauge` facade and `DkMath.lean` import remain
unchanged in GAGE-002. No Value, Dyadic, Landing, FLT, or cyclotomic module
was created.

## 8. Build and audit results

Focused and owner builds succeeded:

```text
lake build DkMath.NumberTheory.Gauge.Exponent       -- 8932 jobs
lake build DkMath.NumberTheory.Gauge                -- 8933 jobs
lake build DkMathTest.NumberTheory.Gauge.Exponent   -- 8934 jobs
lake build DkMathTest.NumberTheory.Gauge.ExponentAxiomAudit -- 8933 jobs
```

The full build succeeded:

```text
lake build DkMath                              -- 10270 jobs
```

`#print axioms` was run for all eleven substantive facade theorems. Every
theorem reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs.

The changed production and test files were scanned for genuine declarations of
`sorry`, `admit`, `sorryAx`, `axiom`, and `unsafe`; none were found.

## 9. Diff summary and next boundary

`git diff --check` succeeded, and the new report and other untracked files were
checked with `git diff --no-index --check /dev/null <file>`.

GAGE-003 may proceed unchanged. It should remain the separate value-side
`ValueGauge` / power-residue layer and must not redefine or merge with the
exponent-side Pascal gauge completed here.

GAGE-002 is complete. Stop before implementing GAGE-003.
