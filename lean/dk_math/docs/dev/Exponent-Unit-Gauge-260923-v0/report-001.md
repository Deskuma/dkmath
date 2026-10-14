# GAGE-001 — Exponent-side gauge facade

Branch: `research/Exponent-Unit-Gauge-260923-v0`
Checkpoint: GAGE-001
Result: **Outcome A — implemented**

## 1. Outcome

The exponent-side gauge facade is implemented as a thin public vocabulary
layer over `DkMath.NumberTheory.PascalPrimeDial` and its existing prime-row
and prime-power-row theorems. No second valuation implementation, gauge
structure, quotient construction, value-side gauge, or FLT-specific module was
introduced.

The facade preserves the existing separation between support predicates and
height formulas. In particular, `PrimeExponentGauge` and
`PrimePowerExponentGauge` are support aliases, while `exponentGaugeHeight` is
the existing Pascal prime-dial height.

## 2. Public API

Production module: `DkMath.NumberTheory.Gauge.Exponent`

```text
DkMath.NumberTheory.Gauge.exponentGaugeHeight
DkMath.NumberTheory.Gauge.PrimeExponentGauge
DkMath.NumberTheory.Gauge.PrimePowerExponentGauge

DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime
DkMath.NumberTheory.Gauge.primeExponentGauge_uniformPrimeDialHeight
DkMath.NumberTheory.Gauge.primeExponentGauge_height_eq_one
DkMath.NumberTheory.Gauge.exponentGaugeHeight_eq_zero_of_row_lt
DkMath.NumberTheory.Gauge.primePowerExponentGauge_of_prime_of_pos
DkMath.NumberTheory.Gauge.exponentGaugeHeight_prime_pow_add_index
DkMath.NumberTheory.Gauge.exponentGaugeHeight_prime_pow_of_not_dvd
```

Definitionally thin mappings:

| facade name | existing owner |
|---|---|
| `exponentGaugeHeight` | `pascalPrimeDialHeight` |
| `PrimeExponentGauge p` | `InnerRowSupportPrime p p` |
| `PrimePowerExponentGauge p e` | `PrimePowerRowSupport p e` |

The theorem bridges reuse the following existing declarations:

| facade theorem | reused theorem |
|---|---|
| `primeExponentGauge_of_prime` | `prime_innerRowSupportPrime_self` |
| `primeExponentGauge_uniformPrimeDialHeight` | `prime_uniformPrimeDialHeight_self` |
| `primeExponentGauge_height_eq_one` | the uniform-height theorem above |
| `exponentGaugeHeight_eq_zero_of_row_lt` | `pascalPrimeDialHeight_eq_zero_of_row_lt` |
| `primePowerExponentGauge_of_prime_of_pos` | `prime_power_rowSupport` |
| `exponentGaugeHeight_prime_pow_add_index` | `pascalPrimeDialHeight_prime_pow_add_index` |
| `exponentGaugeHeight_prime_pow_of_not_dvd` | `prime_power_unitFilteredPrimeDialHeight` |

The public import facade is `DkMath.NumberTheory.Gauge`, and it is exported
from `DkMath.lean`.

## 3. Files changed

```text
DkMath/NumberTheory/Gauge/Exponent.lean
DkMath/NumberTheory/Gauge.lean
DkMath.lean
DkMathTest/NumberTheory/Gauge/Exponent.lean
DkMathTest/NumberTheory/Gauge/ExponentAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-001.md
```

The implementation does not import or conflate
`DkMath.NumberTheory.StructuralArithmetic.PowerGauge` or
`DkMath.NumberTheory.MultiGauge`. Those modules describe different
period/structure or value-side GN observations; this checkpoint exposes only
the Pascal exponent-side vocabulary.

## 4. Tests and builds

The following focused builds succeeded:

```text
lake build DkMath.NumberTheory.Gauge.Exponent
lake build DkMathTest.NumberTheory.Gauge.Exponent
lake build DkMathTest.NumberTheory.Gauge.ExponentAxiomAudit
```

The full public facade build also succeeded:

```text
lake build DkMath
```

Result: `Build completed successfully (10270 jobs)`.

The API test checks all three abbreviations and all seven theorem names, with
examples for prime rows, rows below a prime, prime-power support, the exact
prime-power formula, and the full-depth statement at a prime-unit index.

## 5. Axiom and forbidden-construct audit

The axiom audit was run for all seven new theorems through
`DkMathTest.NumberTheory.Gauge.ExponentAxiomAudit`. Every theorem reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears.

The changed production and test files were scanned for genuine declarations of
`sorry`, `admit`, `sorryAx`, `axiom`, and `unsafe`; none were found. The
intentional `#print axioms` commands are audit commands, not axiom
declarations.

`git diff --check` succeeded for tracked changes. The new files were also
checked with the untracked-file equivalent
`git diff --no-index --check /dev/null <file>`.

## 6. GAGE-002 boundary

No GAGE-002 scope issue was found or changed. The current facade exposes the
existing prime-power support and exponent formulas, but it does not prove a
converse characterization of prime-power rows. That question remains outside
GAGE-001 and may use the new aliases and bridges in a later checkpoint.

GAGE-001 is complete. Stop at the exponent-side facade boundary.
