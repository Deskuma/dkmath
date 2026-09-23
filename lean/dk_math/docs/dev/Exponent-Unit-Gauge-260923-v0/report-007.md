# GAGE-007 — AdditiveLanding facade and v0 closure

Branch: `research/Exponent-Unit-Gauge-260923-v0`

Checkpoint: GAGE-007

Result: **Outcome A — implemented**

## 1. Outcome

The v0 branch now has a neutral landing vocabulary for ordinary power-image
landing, Core-image landing, additive landing, and positive additive landing.
The ValueGauge necessary condition is exposed, the existing TraceOne
arbitrary-power receiver is available through the neutral vocabulary, and the
fixed exponent calibrations are connected at 2, 3, and 5.

The p=7 boundary is intentionally unresolved at the additive-landing level:

> p=7 exponent-gauge resolution is implemented; terminal positive additive
> non-landing is not claimed by this campaign.

No new FLT mathematics, general FLT theorem, carrier identification, or
quotient `K*/(K*)^n` API was added.

## 2. Neutral production owner

Production owner:

```text
DkMath/NumberTheory/Gauge/Landing.lean
```

Namespace: `DkMath.NumberTheory.Gauge`

The module imports `DkMath.NumberTheory.Gauge.Value` and the existing
`DkMath.Lib.NumberTheory.TraceOnePowerLanding`. The latter is neutral: it
depends on the TraceOne lattice/arithmetic library and does not import an FLT
module. Therefore the TraceOne adapter remains in the generic Landing module.
No FLT module is imported by `DkMath.NumberTheory.Gauge`.

## 3. Exact neutral definitions

The following definitions were added without primality assumptions:

```lean
PowerLanding {R : Type*} [Monoid R] (n : ℕ) (a : R) : Prop
CorePowerLanding {R : Type*} [Monoid R] (n : ℕ) (alpha beta : R) : Prop
AdditiveLanding (n x y : ℕ) : Prop
PositiveAdditiveLanding (n x y : ℕ) : Prop
```

The corresponding equations are `a = b ^ n`,
`alpha = beta * gamma ^ n`, `x ^ n + y ^ n = z ^ n`, and the positive
natural-number version of the latter. A thin bridge
`positiveAdditiveLanding_to_additiveLanding` is provided.

## 4. ValueGauge necessary condition

The following theorems were added:

```text
powerLanding_valueGaugePure
positiveAdditiveLanding_valueGaugePure
```

For a nonzero natural `a`, `PowerLanding n a` implies
`ValueGaugePure n a`. The proof reuses `valueGaugePure_pow`; the `n = 0`
case is handled explicitly because `0 ^ 0 = 1` does not imply that the
supplied landing witness is nonzero.

Positive additive landing implies zero ValueGauge defect for the landed sum by
rewriting it to `z ^ n` and using `z > 0`. No converse from zero defect to
additive landing is claimed.

## 5. TraceOne CorePowerLanding adapter

The theorem `corePowerLanding_traceOne_iff` is a definitional wrapper around
`DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff` under the existing
`norm beta ≠ 0` premise. It exposes the same pair of TraceOne coordinate
equations through `CorePowerLanding`; the coordinate reconstruction remains
owned by `TraceOnePowerLanding`.

## 6. FLT-side calibration owner

Production owner:

```text
DkMath/FLT/GaugeLandingCalibration.lean
```

This module imports the neutral Landing API, the existing FLT2 gauge
calibration, the public FLT3 and FLT5 endpoints, and
`DkMath.FLT.Prime.PrimeGaugeBridge`. It is not imported back into the generic
Gauge facade and is not added to the broad historical `DkMath.FLT` aggregator.

### Exponent 2

`primitiveSquareSolution_positiveAdditiveLanding` packages the existing
positivity and equation fields of `PrimitiveSquareSolution` as
`PositiveAdditiveLanding 2`. The theorem
`primitiveSquareSolution_landing_and_oriented_gauge_split` combines that
landing with the existing GAGE-005 oriented `PrimitiveSquareLandingGaugeSplit`
disjunction. The square split itself was not reproved or modified. The
concrete `(3, 4, 5)` landing is tested.

### Exponents 3 and 5

`not_positiveAdditiveLanding_three` and
`not_positiveAdditiveLanding_five` only unpack a positive landing witness and
apply the existing completed endpoints:

```text
DkMath.FLT.Three.fermatThree_no_positive_solution
DkMath.FLT.Five.fermatFive_no_positive_solution
```

No FLT3 or FLT5 proof tower was changed.

### Exponent 7

`primeExponentGauge_seven_boundary` exposes only `PrimeExponentGauge 7`,
already justified by the Pascal prime-row API. The existing GAGE-006 p=7
cyclotomic/TraceOne scalar calibration remains available through
`PrimeGaugeBridge`. There is no theorem of the form
`¬ PositiveAdditiveLanding 7 x y`.

## 7. Relationship to PrimeGaugeBridge

The calibration owner imports `DkMath.FLT.Prime.PrimeGaugeBridge` only to keep
the odd-prime resolution chain discoverable alongside the landing
calibrations. The bridge continues to provide the established route:

```text
PrimeExponentGauge p
  -> cyclotomic homogeneous evaluation
  -> cyclotomic ideal absNorm / GTail scalar
  -> ValueGauge coordinates
  -> TraceOne scalar norm
```

GAGE-007 adds no carrier equality, class-group result, unit-sector result, or
new odd-prime resolver proof.

## 8. Files changed

```text
DkMath/NumberTheory/Gauge/Landing.lean
DkMath/NumberTheory/Gauge.lean
DkMath/FLT/GaugeLandingCalibration.lean
DkMathTest/NumberTheory/Gauge/Landing.lean
DkMathTest/NumberTheory/Gauge/LandingAxiomAudit.lean
DkMathTest/FLT/GaugeLandingCalibration.lean
DkMathTest/FLT/GaugeLandingCalibrationAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
docs/dev/Exponent-Unit-Gauge-260923-v0/report-007.md
```

## 9. Focused and full builds

All requested owner and test builds completed successfully:

```text
lake build DkMath.NumberTheory.Gauge.Landing
-- Build completed successfully (8933 jobs).
lake build DkMath.NumberTheory.Gauge
-- Build completed successfully (8953 jobs).
lake build DkMathTest.NumberTheory.Gauge.Landing
-- Build completed successfully (8934 jobs).
lake build DkMathTest.NumberTheory.Gauge.LandingAxiomAudit
-- Build completed successfully (8934 jobs).
lake build DkMath.FLT.GaugeLandingCalibration
-- Build completed successfully (9088 jobs).
lake build DkMathTest.FLT.GaugeLandingCalibration
-- Build completed successfully (9089 jobs).
lake build DkMathTest.FLT.GaugeLandingCalibrationAxiomAudit
-- Build completed successfully (9089 jobs).
lake build DkMath
-- Build completed successfully (10276 jobs).
```

The full build retains unrelated pre-existing repository warnings, including
an existing research-file `sorry` warning outside the GAGE-007 files.

## 10. Axiom and safety audits

`#print axioms` was run for every substantive new theorem in both production
modules and in the two audit modules. The reports contain only existing
kernel/library dependencies (`propext`, `Classical.choice`, and `Quot.sound`
where applicable); no new unsafe shortcut or declared axiom was introduced.

The new production/test Lean files were scanned for `sorry`, `admit`,
`sorryAx`, declared `axiom`, and `unsafe`; no matches were found. `git diff
--check` and `git diff --no-index --check` for the new files produced no
whitespace diagnostics.

## 11. Diff and closeout

The diff is limited to the neutral Landing owner, the public Gauge import,
the separate FLT calibration owner, focused tests/audits, ROADMAP status, and
this report. No commit, push, merge, pull request, CI action, GAGE-005 change,
or GAGE-006 internal change was performed.

ROADMAP now records that GAGE-000 through GAGE-007 have been executed. This is
v0 closure for the bounded semantic/API campaign, not a claim of general FLT
or p=7 additive non-landing.

## 12. Deferred research

- universal additive-landing obstruction for prime exponents beyond the
  completed 3 and 5 endpoints;
- terminal positive additive non-landing at exponent 7;
- general-FLT terminal contradiction;
- class-group and unit-sector elimination for arbitrary primes;
- a quotient `K*/(K*)^n` API;
- analytic interpretations of dyadic refinement.

GAGE-007 is the final checkpoint of this v0 campaign.
