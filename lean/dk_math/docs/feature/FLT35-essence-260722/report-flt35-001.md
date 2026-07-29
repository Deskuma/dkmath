# FLT3 / FLT5 quadratic essence implementation report 001

- Date: 2026-07-22
- Scope: F35-002 through F35-005
- Result: PASS

## Implemented checkpoint

The neutral trace-one quadratic coordinate ring and both exponent-specific
bridges are now implemented.  The existing FLT3 and FLT5 endpoint theorem
statements and proof bodies were not changed.

### F35-002: neutral core

Added `DkMath/NumberTheory/TraceOneQuadratic.lean`.

The module defines `TraceOneInt s`, its coordinate operations, and honest
`AddCommGroup`, `AddGroupWithOne`, and `CommRing` instances.  It proves:

- `traceOne_tau_sq`
- `traceOne_conj_invol`
- `traceOne_conj_mul`
- `traceOne_mul_conj`
- `traceOne_norm_mul`
- `four_mul_traceOneNorm_eq_discriminant`
- `traceOneNorm_neg_one`
- `traceOneNorm_one`

No generic `IsDomain`, PID, UFD, or Euclidean-domain instance was introduced.

### F35-003: FLT3 bridge

Added `DkMath/FLT/ThreeTraceOneBridge.lean` with:

- `S0_nat_eq_traceOneNorm_negOne`
- `S0_int_eq_traceOneNorm_negOne`
- `GN_three_sub_eq_traceOneNorm_negOne`
- `eisensteinNorm_shift_eq_traceOneNorm_negOne`

Thus the direct cubic kernel and its existing shifted Eisenstein presentation
meet at `TraceOneInt (-1)` without changing the native conditional FLT3 route.

### F35-004: FLT5 bridge

Added `DkMath/FLT/Five/TraceOneBridge.lean` with:

- `goldenToTraceOne`
- `goldenNorm_eq_traceOneNorm_one`
- `GoldenNorm_eq_traceOneNorm_one`
- `GN5_eq_traceOneNorm_squareLink`

The map is coordinate-preserving only.  `GoldenInt` remains the production
type, so its domain and Euclidean instances and the completed FLT5 tower are
unchanged.

### F35-005: facade and audit

Added:

- `DkMath/FLT/QuadraticEssence.lean`
- `DkMathTest/FLT/QuadraticEssence.lean`

The facade exposes only the proved exponent-3 and exponent-5 specializations.
It deliberately contains no general-prime theorem.  Public imports were wired
through `DkMath.FLT.Five` and `DkMath.FLT`.

The new axiom audit reports only the standard Mathlib axioms among `propext`,
`Classical.choice`, and `Quot.sound`; it reports no `sorryAx` for the new
theorems.

## Verification

The following commands passed from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.TraceOneQuadratic
lake build DkMath.FLT.ThreeTraceOneBridge \
  DkMath.FLT.Five.TraceOneBridge \
  DkMath.FLT.QuadraticEssence \
  DkMathTest.FLT.QuadraticEssence
lake build DkMath.FLT DkMath.FLT.Five DkMathTest.FLT.Five.CheckAxioms
```

The last command confirms that the public aggregator, the complete FLT5 tower,
and its pre-existing axiom audit still build after the new imports.

## Honest boundary and next checkpoint

This report closes F35-002 through F35-005.  It does not claim completion of
F35-006 through F35-009.

In particular, the Mathlib-only full FLT5 standalone artifact has not yet been
generated.  That work is a separate provenance-sensitive checkpoint requiring
an import-graph-validated manifest, deterministic flattener, isolated build,
checksum, endpoint comparison, and saved build/axiom logs.  The current
`DkMath.FLT.Five.Standalone` remains the small GN5 seed described in the design.

Recommended next checkpoint: implement F35-006 first, review the exact flattened
source order and generator contract, and only then commit the large generated
artifact for F35-007 and its comparator/trust audit for F35-008.
