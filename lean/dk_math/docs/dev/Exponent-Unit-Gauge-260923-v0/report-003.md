# GAGE-003 — ValueGauge / local power residue

Branch: `research/Exponent-Unit-Gauge-260923-v0`
Checkpoint: GAGE-003
Result: **Outcome A — implemented**

## 1. Outcome

The value-side gauge is now publicly available as the prime-valuation residue
vector modulo `n`. The implementation is a semantic facade over the existing
StructuralArithmetic prime-coordinate projection; no second valuation or
modulo/projection engine was introduced.

The exponent-side Pascal Gauge remains separate:

```text
ExponentGauge (Pascal side) != StructuralArithmetic.PowerGauge
ValueGauge (value side) = semantic facade over StructuralArithmetic prime coordinates
```

No dyadic, FLT2, cyclotomic, landing, quotient, or general-FLT module was
implemented.

## 2. Existing APIs reused

The production module reuses these exact owners and declarations:

| existing API | use in GAGE-003 |
|---|---|
| `StructuralArithmetic.PrimeIndex` | prime-coordinate index type `ValueGaugePrime` |
| `StructuralArithmetic.projectExponent` | local residue `v_p(a) % n` |
| `StructuralArithmetic.projectExponent_period_zero` | period-zero local boundary |
| `StructuralArithmetic.projectExponent_period_one` | period-one local boundary |
| `StructuralArithmetic.projectExponent_period_mul` | zero residue of a perfect power |
| `StructuralArithmetic.primeExponentCoordinates` | underlying raw valuation vector |
| `StructuralArithmetic.projectPrimeCoordinates` | full value-side residue vector |
| `StructuralArithmetic.projectPrimeCoordinates_period_zero` | raw-vector period-zero boundary |
| `StructuralArithmetic.projectPrimeCoordinates_period_one` | zero-vector period-one boundary |
| `StructuralArithmetic.padicValNat_pow` | valuation of a nonzero power in the calibration test |
| `Lib.NumberTheory.padicValNat_pow` | valuation-of-power proof in the production facade |
| `StructuralArithmetic.projectPrimeCoordinates_mul_pow` | multiplication by an `n`-th-power conservation law |

The production import is limited to
`DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates` and
`DkMath.Lib.NumberTheory.PadicValNat`; it has no FLT import.

## 3. Public ValueGauge API

Production module: `DkMath.NumberTheory.Gauge.Value`

```text
ValueGaugePrime
valueGaugeResidue
valueGaugeCoordinates
ValueGaugePure

valueGaugeResidue_eq_mod
valueGaugeCoordinates_apply
valueGaugeResidue_period_zero
valueGaugeResidue_period_one
valueGaugeCoordinates_period_zero
valueGaugeCoordinates_period_one
valueGaugeResidue_pow_eq_zero
valueGaugeCoordinates_pow_eq_zero
valueGaugeCoordinates_mul_pow
valueGaugePure_pow
not_valueGaugePure_zero
```

The definitions are definitionally thin:

```text
ValueGaugePrime = StructuralArithmetic.PrimeIndex
valueGaugeResidue n p a
  = projectExponent n (padicValNat p.1 a)
valueGaugeCoordinates n a
  = projectPrimeCoordinates n a
```

The purity predicate is intentionally nonzero-aware:

```text
ValueGaugePure n a :=
  a != 0 ∧ valueGaugeCoordinates n a = fun _ => 0
```

Thus the conventional valuation behavior at zero is never silently promoted
to ordinary nonzero perfect-power factorization data.

## 4. Proof and reuse map

- `valueGaugeResidue_eq_mod` is `rfl` after unfolding the semantic alias.
- `valueGaugeCoordinates_apply` is `rfl` after unfolding the two coordinate
  aliases.
- The four period-zero/period-one theorems directly reuse the corresponding
  `projectExponent` and `projectPrimeCoordinates` boundary theorems.
- `valueGaugeResidue_pow_eq_zero` reuses
  `DkMath.Lib.NumberTheory.padicValNat_pow` and then applies
  `projectExponent_period_mul`.
- `valueGaugeCoordinates_pow_eq_zero` is the pointwise vector form of the
  local power theorem.
- `valueGaugeCoordinates_mul_pow` is a direct wrapper over
  `projectPrimeCoordinates_mul_pow`; its hypotheses are exactly the required
  nonzero hypotheses for the residual and the multiplier base.
- `valueGaugePure_pow` packages nonzeroness of the power with the vector zero
  theorem.
- `not_valueGaugePure_zero` discharges the explicit nonzero guard without
  making any claim about the valuation convention at zero.

## 5. Boundary behavior

The public boundary theorems and tests cover the required cases:

- `n = 0`: `projectExponent 0 v = v`; the raw valuation vector is retained.
- `n = 1`: every local and vector residue is zero.
- `a = 0`: `ValueGaugePure n 0` is false by definition; no perfect-power
  statement is made for zero.
- `a = 1`: the nonzero perfect-power theorem gives purity for both period `0`
  and period `1`.

The forward power theorem is valid for `n = 0` and `n = 1` under its explicit
nonzero base hypothesis, exactly through the existing valuation and projection
owners.

## 6. Optional converse reconnaissance

The pinned Mathlib tree was searched for a direct theorem turning

```text
a != 0 and every prime valuation of a is divisible by n
-> exists b, a = b ^ n
```

No short direct theorem matching this value-side API was found. Mathlib does
provide factorization reconstruction primitives such as
`Nat.factorization_pow`, `Nat.prod_factorization_pow_eq_self`, and
`Nat.eq_pow_of_factorization_eq_single`, but combining them into a general
perfect-power reconstruction would be a new proof layer rather than a thin
facade. That converse is therefore deferred and is not required for GAGE-003.

## 7. Calibration examples

`DkMathTest.NumberTheory.Gauge.Value` verifies:

- `36` is `ValueGaugePure 2 36` via the nonzero square theorem;
- `72` is not `ValueGaugePure 2 72`, using the coordinate at prime `2` and
  the existing valuation multiplication theorem to establish `v₂(72) = 3`;
- `27` is `ValueGaugePure 3 27`;
- multiplying `7` by `5^3` preserves the period-3 value vector;
- periods `0` and `1`, values `0` and `1`, and the GAGE-003 boundary laws.

## 8. Files changed

```text
DkMath/NumberTheory/Gauge/Value.lean
DkMath/NumberTheory/Gauge.lean
DkMathTest/NumberTheory/Gauge/Value.lean
DkMathTest/NumberTheory/Gauge/ValueAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-003.md
```

No `DkMath.lean` change was needed because the existing public Gauge facade is
already exported there.

## 9. Builds and audits

All requested builds succeeded:

```text
lake build DkMath.NumberTheory.Gauge.Value                 -- 8928 jobs
lake build DkMath.NumberTheory.Gauge                       -- 8936 jobs
lake build DkMathTest.NumberTheory.Gauge.Value              -- 8937 jobs
lake build DkMathTest.NumberTheory.Gauge.ValueAxiomAudit    -- 8929 jobs
lake build DkMath                                                -- 10273 jobs
```

`#print axioms` was run for all eleven new substantive ValueGauge theorems.
Every theorem reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs. The builds replay an existing style linter warning in
`StructuralArithmetic/PrimeCoordinates.lean`; it is outside the changed
GAGE-003 production code and does not affect the successful builds.

The changed production and test files were scanned for genuine declarations of
`sorry`, `admit`, `sorryAx`, `axiom`, and `unsafe`; none were found.

## 10. Diff summary and next boundary

`git diff --check` succeeded, and the new ValueGauge, test, audit, and report
files were checked with `git diff --no-index --check /dev/null <file>`.

GAGE-004 may proceed unchanged. It should remain the separate dyadic/midpoint
calibration and must not redefine the value-side coordinate projection or
merge it with the exponent-side Pascal Gauge.

GAGE-003 is complete. Stop before implementing GAGE-004.
