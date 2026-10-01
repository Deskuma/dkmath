# GAGE-004 — Dyadic midpoint gauge

Branch: `research/Exponent-Unit-Gauge-260923-v0`

Checkpoint: GAGE-004
Result: **Outcome A — implemented**

## 1. Outcome

The dyadic/midpoint calibration layer is implemented as a small public
module. It provides the requested division-free scaled defect, its exact
d=2/3/4 calibrations, a characteristic-zero field half-unit identity, and
thin endpoint bridges to the existing `PowerGapBeam` API.

The identity

```text
scaledMidpointDefect 2 x u = 0
```

is recorded only as midpoint closure. It is not an FLT2 theorem, and no FLT2
factor split, cyclotomic construction, or landing theorem was added.

## 2. Public API

Production module: `DkMath.NumberTheory.Gauge.Dyadic`

Namespace: `DkMath.NumberTheory.Gauge`

```text
scaledMidpointDefect
scaledMidpointDefect_two
scaledMidpointDefect_three
scaledMidpointDefect_four

midpointSquareIdentity
midpointSquareIdentity_real_halfUnit

powerGap_self_add
powerBeam_two_self_add
midpointSquareDifference_eq_gap_mul_beam
midpointSquareDifference_eq_increment_beam
```

The public `DkMath.NumberTheory.Gauge` facade now imports `Dyadic`.

## 3. Division-free defect and low-degree calibration

The production definition is exactly division-free:

```lean
def scaledMidpointDefect {R : Type*} [CommRing R]
    (d : ℕ) (x u : R) : R :=
  (2 : R) ^ (d - 1) * ((x + u) ^ d - x ^ d)
    - (d : R) * u * (2 * x + u) ^ (d - 1)
```

The three calibration theorems are proved by `ring` over the weakest
practical `CommRing` assumption:

```text
scaledMidpointDefect 2 x u = 0
scaledMidpointDefect 3 x u = u^3
scaledMidpointDefect 4 x u = 4*u^3*(2*x+u)
```

The tests include the requested concrete values
`scaledMidpointDefect 3 1 1 = 1` and
`scaledMidpointDefect 4 1 1 = 12`.

## 4. Half-unit identity

The generic identity is exposed over `[Field K] [CharZero K]`:

```text
(x + u)^2 - x^2 = 2*u*(x + u/2)
```

The real bridge `midpointSquareIdentity_real_halfUnit` unfolds and reuses the
existing `DkMath.CosmicFormula.HalfUnitZeroConjugate.halfUnit` definition; no
second half-unit implementation was introduced.

## 5. PowerGapBeam reuse map

The endpoint bridges are generic over `CommRing` and reuse the existing
declarations from `DkMath.CosmicFormula.PowerGapBeam`:

- `powerGap_self_add` reduces `powerGap x (x + u)` to `u` through
  `powerGap_eq_sub`.
- `powerBeam_two_self_add` reduces the quadratic beam through
  `powerBeam_two` to `2*x + u`.
- `midpointSquareDifference_eq_gap_mul_beam` is the d=2 instance of the
  existing `pow_sub_pow_eq_gap_mul_powerBeam` theorem.
- `midpointSquareDifference_eq_increment_beam` combines those bridges to give
  `(x + u)^2 - x^2 = u*(2*x + u)`.

No duplicate power-difference factorization was added.

## 6. Generic expansion and positivity reconnaissance

The generic odd-exponent correction expansion was investigated but not added:
the existing `DkMath.Algebra.DiffPow` API supplies the ordinary gap
factorization, while a centered/binomial correction theorem would be a new
proof layer rather than a proof-thin facade.

Positivity and uniqueness were also deferred. The d=2 vanishing result alone
does not establish a positive correction or uniqueness statement, and no
such claim is made here. No dyadic half-step hierarchy or self-similarity
theorem was introduced.

## 7. Tests and audits

`DkMathTest.NumberTheory.Gauge.Dyadic` checks:

- symbolic d=2, d=3, and d=4 identities over `ℤ`;
- the concrete d=3 and d=4 values;
- the half-unit identity over `ℚ` and the real `halfUnit` bridge;
- the endpoint gap, quadratic beam, and reduced square-difference identity.

`DkMathTest.NumberTheory.Gauge.DyadicAxiomAudit` runs `#print axioms` for all
nine substantive production theorems. No `sorryAx` occurs. The reports are
the expected kernel/library dependencies (`propext`, and for field or
finite-sum results the existing `Classical.choice`/`Quot.sound` dependencies).

## 8. Files changed

```text
DkMath/NumberTheory/Gauge/Dyadic.lean
DkMath/NumberTheory/Gauge.lean
DkMathTest/NumberTheory/Gauge/Dyadic.lean
DkMathTest/NumberTheory/Gauge/DyadicAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-004.md
```

## 9. Builds and scans

The requested focused and facade builds succeeded:

```text
lake build DkMath.NumberTheory.Gauge.Dyadic
lake build DkMath.NumberTheory.Gauge
lake build DkMathTest.NumberTheory.Gauge.Dyadic
lake build DkMathTest.NumberTheory.Gauge.DyadicAxiomAudit
lake build DkMath
```

The build replayed the pre-existing deprecation warning in
`CosmicFormula/HalfUnitZeroConjugate.lean` and the pre-existing
`haveI` style-linter warning in
`StructuralArithmetic/PrimeCoordinates.lean`; neither file was changed by
GAGE-004.

The changed Lean files were scanned for genuine declarations of `sorry`,
`admit`, `sorryAx`, `axiom`, and `unsafe`; none were found. `git diff --check`
was run for tracked changes, and the new report was checked with
`git diff --no-index --check /dev/null docs/dev/Exponent-Unit-Gauge-260923-v0/report-004.md`.

## 10. Next boundary

GAGE-004 is complete. GAGE-005 may proceed from this stable dyadic facade,
while keeping the FLT2 landing problem, generic odd correction, positivity,
and uniqueness as separate future work.

Stop at the GAGE-004 boundary.
