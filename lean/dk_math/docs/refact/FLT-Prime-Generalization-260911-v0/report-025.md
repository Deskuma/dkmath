# FLT prime-generalization Phase 25 report

Status:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
PGEN-PRIME-TRACEONE-IDEAL-POWER-GREEN
```

## Implemented

- Added the signed-prime adapter
  `DkMath.NumberTheory.TraceOneQuadratic.signedPrimeDiscriminantPacket`.
  It packages `discr_signedPrimeParameter` and
  `signedPrimeDiscriminant_natAbs` into `PrimeDiscriminantPacket`.
- Promoted the Nat/Int bridge
  `DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell` to the
  neutral GTail cyclotomic module and reused it from the Phase-24 coordinate
  coprimality proof.
- Added the neutral coordinate-strip lemma
  `coordinate_isCoprime_of_eq_discrAxis_mul` by a direct Bézout calculation.
- Added the neutral principal-ideal identities
  `span_mul_span_conj_eq_span_norm` and
  `span_mul_span_conj_eq_pow_of_norm_eq_pow`.
- Added `PrimeTraceOneStrippedIdealPacket` and
  `nonempty_primeTraceOneStrippedIdealPacket` in
  `DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean`.
  The packet consumes `PrimeAdicFactorPacket` and
  `PrimeTraceOneCoordinatePacket`, constructs the one-axis residual, proves
  residual coordinate primitivity and conjugate-ideal coprimality, and extracts
  a nonzero ideal `p`-th power using the Phase-15 factor API.
- Added API, p=3/5/7/11/13 architecture regressions, and axiom audit files.
  The p=7 regression also replays the existing
  `SevenQuadraticResidualPacket.norm_is_seventh_power` endpoint.

## Exact API audit

`PrimeTraceOneStrippedIdealApiAudit.lean` records the checkout-local
signatures used by the implementation, including:

- `PrimeAdicFactorPacket`, `PrimeAdicPowerSplit`,
  `primeAdicPowerSplit_of_packet`, `residual_eq`, and `prime_not_dvd_b`;
- `PrimeTraceOneCoordinatePacket`, `coord`, `coord_norm_eq`, and
  `prime_packet_coordinate_isCoprime`;
- `PrimeDiscriminantPacket`, `discr_signedPrimeParameter`,
  `signedPrimeDiscriminant_natAbs`, the signed-prime adapter, and the terminal
  axis-strip theorem;
- `ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal`,
  `traceOne_mul_conj`, `traceOneRat_no_rational_root`,
  `traceOneRat_isDedekindDomain`, and
  `exists_eq_pow_of_isCoprime_mul_eq_pow`;
- the exact `Ideal.span` singleton multiplication/power and nonzero-divisor
  declarations used by the neutral ideal proof.

## Boundary

The new packet stops at an ideal `p`-th power.  It does not assert
principalization, class-group `p`-torsion-freeness, unit-sector elimination,
regular-prime theory, or FLT.

## Validation

The instruction-025 focused build passed for all requested targets:

```text
DkMath.NumberTheory.TraceOneDiscriminantAxis
DkMath.NumberTheory.TraceOneConjugateCoprime
DkMath.NumberTheory.TraceOneQuadraticField
DkMath.NumberTheory.CyclotomicQRTraceOneBridge
DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
DkMath.FLT.Prime.AdicPowerSplit
DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealApiAudit
DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealProbe
DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealAxiomAudit
DkMath.FLT.Seven
```

The fresh build log had no `warning:` entries.  The Phase-25 production and
test source scan found no `sorry`, `sorryAx`, `admit`, explicit `axiom`, or
`unsafe`; `git diff --check` also passed.

The axiom audit reports only the standard inherited dependencies
`propext`, `Classical.choice`, and `Quot.sound` for the new public endpoints.
