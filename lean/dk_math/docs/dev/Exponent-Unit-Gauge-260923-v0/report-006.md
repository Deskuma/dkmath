# GAGE-006 — Cyclotomic gauge bridge

Branch: `research/Exponent-Unit-Gauge-260923-v0`

Checkpoint: GAGE-006

Result: **Outcome A — implemented**

## 1. Outcome

The Pascal-side `PrimeExponentGauge p` is now a public entry point into the
existing prime cyclotomic resolver. The bridge exposes the route:

```text
PrimeExponentGauge p
  -> p is prime
  -> homogeneous prime cyclotomic evaluation
  -> cyclotomic principal-ideal absNorm
  -> GTail scalar
  -> ValueGauge coordinates
  -> TraceOne scalar norm
```

The implementation is a semantic bridge only. It reuses the existing
cyclotomic, norm, ideal, and TraceOne identities. It claims scalar
compatibility, not equality or isomorphism of cyclotomic and TraceOne carrier
objects or ideals.

## 2. Production owner and facade

Production owner:

```text
DkMath/FLT/Prime/PrimeGaugeBridge.lean
```

Namespace: `DkMath.FLT.Prime`

The public `DkMath.FLT.Prime` import facade now imports
`DkMath.FLT.Prime.PrimeGaugeBridge`. `DkMath.NumberTheory.Gauge` remains free
of FLT imports, and the GAGE-005 FLT2 owner is not imported.

## 3. Exact pinned declarations reused

The bridge uses these existing declarations without reproving their algebra:

```text
DkMath.NumberTheory.innerRowSupportPrime_prime
DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime
DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell
DkMath.CosmicFormula.GTailCyclotomicHomEval_prime_eq_shell
DkMath.CFBRC.cyclotomicLinearFactorIdeal_absNorm_eq_GN
DkMath.FLT.Prime.PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
DkMath.FLT.Prime.TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_three
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_five
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
```

The existing `PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual`
theorem remains available and was not duplicated or modified; the high-level
packet result directly reuses the already-composed packet ideal equation.

## 4. PrimeExponentGauge and primality

`PrimeExponentGauge.prime` unwraps the existing
`InnerRowSupportPrime p p` abbreviation through
`innerRowSupportPrime_prime`. No duplicate prime-proof structure is stored.

The homogeneous evaluation theorem is:

```text
primeExponentGauge_GTail_eq_cyclotomicHomEval
```

It first rewrites `GTail p 1` to the cyclotomic shell and then uses the
existing prime cyclotomic coefficient theorem. No nonzero-gap premise is
introduced.

## 5. Ideal norm and ValueGauge conservation

The generic resolver is:

```text
primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail
```

It derives `p.Prime` from the exponent gauge, constructs the corresponding
`Fact p.Prime` witness locally, and passes that witness to the existing
`cyclotomicLinearFactorIdeal_absNorm_eq_GN` theorem. The theorem's ambient
`Fact` parameter is required by the existing ideal-carrier API; no new prime
data structure is introduced.

The ValueGauge-level conservation theorem is:

```text
primeExponentGauge_valueGaugeCoordinates_cyclotomicIdeal_eq_GTail
```

It is a direct rewrite through the scalar ideal-norm equality for arbitrary
period `n`; it adds no valuation proof.

## 6. PrimeAdicFactorPacket integration

The packet projection is:

```text
PrimeAdicFactorPacket.exponentGauge
```

It applies `primeExponentGauge_of_prime P.prime`. The composed theorem

```text
PrimeAdicFactorPacket.gauge_resolves_to_cyclotomicIdeal
```

returns the exponent gauge together with the already-proved equation

```text
g * Ideal.absNorm(cyclotomicLinearFactorIdeal ζ g u) = x ^ p.
```

The packet factor equation itself was not reproved.

## 7. TraceOne scalar conservation

The generic scalar transport theorem is:

```text
primeGauge_valueGaugeCoordinates_traceOne_eq_cyclotomicIdeal
```

It rewrites through
`TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm` and preserves
all ValueGauge coordinates. The composed resolver is:

```text
primeExponentGauge_valueGaugeCoordinates_traceOne_eq_GTail
```

This is a scalar statement only. The implementation does not identify
TraceOne elements, cyclotomic elements, or their ideals.

## 8. p = 3, 5, 7 calibration

The following conjunction-valued calibrations pair each exponent gauge with
the existing dedicated scalar norm equality:

```text
primeExponentGauge_three_calibration
primeExponentGauge_five_calibration
primeExponentGauge_seven_calibration
```

The p = 5 calibration uses the existing square-link TraceOne presentation;
the optional GoldenNorm presentation was not duplicated in this bridge.

Focused tests instantiate `CyclotomicField p ℚ` for p = 3, 5, 7, verify the
symbolic homogeneous evaluation, ideal resolver, ValueGauge coordinate
preservation, TraceOne transport, packet projection, and all three fixed-prime
calibrations.

## 9. Files changed

```text
DkMath/FLT/Prime/PrimeGaugeBridge.lean
DkMath/FLT/Prime.lean
DkMathTest/FLT/Prime/PrimeGaugeBridge.lean
DkMathTest/FLT/Prime/PrimeGaugeBridgeAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-006.md
```

No proofs in `GTailCyclotomic`, `CyclotomicNorm`, `CyclotomicIdeal`,
`PrimeCyclotomicIdeal`, `PrimeCyclotomicTraceOne`, or
`PrimeCyclotomicCalibration` were modified.

## 10. Builds and audits

Focused production build:

```text
lake build DkMath.FLT.Prime.PrimeGaugeBridge
-- Build completed successfully (9048 jobs).
```

Focused facade, test, and axiom-audit build:

```text
lake build DkMath.FLT.Prime.PrimeGaugeBridge DkMath.FLT.Prime \
  DkMathTest.FLT.Prime.PrimeGaugeBridge \
  DkMathTest.FLT.Prime.PrimeGaugeBridgeAxiomAudit
-- Build completed successfully (9096 jobs).
```

Full build:

```text
lake build DkMath
-- Build completed successfully (10275 jobs).
```

The axiom audit covers all eleven substantive new public theorems. They report
only the existing kernel/library dependencies (`propext`, `Classical.choice`,
and `Quot.sound` where applicable); no `sorryAx` occurs in the new bridge.
The full repository retains unrelated pre-existing warnings, including the
existing `ZsigmondyCyclotomicResearch` sorry warning.

## 11. Safety and diff checks

The changed production and test Lean files were scanned for `sorry`, `admit`,
`sorryAx`, declared `axiom`, and `unsafe`; no matches were found. `git
diff --check` and `git diff --no-index --check` were run for tracked and new
files; no whitespace errors were reported.

The final status contains only the four new bridge/test/report paths and the
facade import modification. No commit, push, or CI action was performed.

## 12. Boundary

Only scalar ValueGauge compatibility is claimed. No class-group theorem,
unit-sector result, AdditiveLanding implementation, FLT2 change, FLT7 proof,
or general-FLT theorem was added.

GAGE-007 may proceed unchanged from this bridge and the existing neutral
landing APIs. Stop after GAGE-006.
