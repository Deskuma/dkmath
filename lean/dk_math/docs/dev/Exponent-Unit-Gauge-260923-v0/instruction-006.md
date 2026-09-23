# GAGE-006 — Cyclotomic gauge bridge

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-005.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-005.md
~~~

## Objective

Connect the completed exponent-side Pascal gauge to the existing PR #105 cyclotomic / norm / ideal / TraceOne conservation chain.

This checkpoint is a semantic bridge. Do not re-prove cyclotomic identities, norm formulas, ideal norms, or fixed-prime TraceOne calibrations.

The key public route should be visibly readable as:

~~~text
PrimeExponentGauge p
  -> p is prime
  -> homogeneous prime cyclotomic carrier
  -> GTail/GN scalar
  -> cyclotomic principal-ideal absNorm
  -> same ValueGauge coordinates
  -> TraceOne scalar norm
~~~

## Required production owner

Create:

~~~text
DkMath/FLT/Prime/PrimeGaugeBridge.lean
~~~

Use namespace:

~~~lean
namespace DkMath.FLT.Prime
~~~

Import the smallest practical set beginning from:

~~~text
DkMath.NumberTheory.Gauge
DkMath.Lib.Cosmic.GTailCyclotomic
DkMath.FLT.Prime.PrimeCyclotomicIdeal
DkMath.FLT.Prime.PrimeCyclotomicTraceOne
DkMath.FLT.Prime.PrimeCyclotomicCalibration
~~~

Do not import `DkMath.FLT.Two.GaugeCalibration`.

After implementation, add `PrimeGaugeBridge` to the public `DkMath/FLT/Prime.lean` import facade if this matches repository convention.

## Step 0 — pinned API audit

Before coding, confirm the exact declarations available on this branch. Expected owners include:

~~~text
DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell
DkMath.CosmicFormula.GTailCyclotomicHomEval_prime_eq_shell
DkMath.CFBRC.cyclotomicLinearFactorIdeal_absNorm_eq_GN
DkMath.FLT.Prime.PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual
DkMath.FLT.Prime.PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
DkMath.FLT.Prime.TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm
DkMath.FLT.Prime.TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_three
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_five
DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
~~~

Do not assume spelling/signatures from this instruction if the pinned source differs. Record the exact declarations used in report-006.md.

## Part A — recover primality from ExponentGauge

Add a tiny bridge theorem if useful:

~~~lean
theorem PrimeExponentGauge.prime
    {p : ℕ} (h : DkMath.NumberTheory.Gauge.PrimeExponentGauge p) :
    p.Prime := ...
~~~

or an equivalent repository-style theorem.

Because `PrimeExponentGauge` abbreviates `InnerRowSupportPrime p p`, this must be proof-thin.

Do not separately store a duplicate prime proof structure.

## Part B — ExponentGauge to homogeneous cyclotomic evaluation

This is the first genuinely semantic bridge.

Prefer a theorem over `CommRing R` of the shape:

~~~lean
theorem primeExponentGauge_GTail_eq_cyclotomicHomEval
    {R : Type*} [CommRing R] {p : ℕ}
    (hGauge : DkMath.NumberTheory.Gauge.PrimeExponentGauge p)
    (x u : R) :
    DkMath.CosmicFormula.GTail p 1 x u =
      DkMath.CosmicFormula.GTailCyclotomicHomEval
        p (Polynomial.cyclotomic p ℤ) x u := ...
~~~

The proof should use:

~~~text
GTail_one_eq_GTailCyclotomicShell
GTailCyclotomicHomEval_prime_eq_shell
~~~

with primality extracted from `hGauge`.

This theorem is preferable to merely restating `GTail = shell`, because the homogeneous cyclotomic evaluation actually requires the prime property supplied by the exponent gauge.

Do not impose an unnecessary nonzero-gap hypothesis.

## Part C — ExponentGauge to cyclotomic ideal norm

Add a generic resolver theorem for natural gap/base data.

Target semantic shape:

~~~text
PrimeExponentGauge p
+ cyclotomic field K for p
+ primitive p-th root zeta
--------------------------------
Ideal.absNorm(cyclotomicLinearFactorIdeal zeta g u)
  = GTail p 1 g u
~~~

Implementation guidance:

1. extract `hp : p.Prime` from `hGauge`;
2. install locally:

~~~lean
letI : Fact p.Prime := ⟨hp⟩
~~~

3. reuse the existing `cyclotomicLinearFactorIdeal_absNorm_eq_GN` theorem;
4. only bridge `GN` to `GTail p 1` through the existing definitional/API relation.

Do not re-prove the field norm or ideal norm theorem.

Suggested semantic name:

~~~text
primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail
~~~

or equivalent.

## Part D — GaugeConservationKernel at the value-gauge level

Use the GAGE-003 ValueGauge API to expose that the resolver preserves the full prime-coordinate residue observation.

For arbitrary period `n`, prove:

~~~text
valueGaugeCoordinates n
  (Ideal.absNorm (cyclotomicLinearFactorIdeal ...))
=
valueGaugeCoordinates n (GTail p 1 g u)
~~~

under the same hypotheses as Part C.

This should be a rewrite through the scalar equality from Part C, not a new valuation proof.

If useful and essentially free, add the pointwise residue form:

~~~text
valueGaugeResidue n q idealAbsNorm
  = valueGaugeResidue n q residualGTail
~~~

but do not duplicate both forms if one is enough.

This theorem is the v0 public realization of the name `GaugeConservationKernel`.

Do not define a large `GaugeConservationKernel` structure merely to hold one equality.

## Part E — PrimeAdicFactorPacket integration

Expose that the existing FLT prime-adic packet itself supplies the exponent gauge.

Target:

~~~lean
theorem PrimeAdicFactorPacket.exponentGauge
    (P : PrimeAdicFactorPacket p g u x) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge p :=
  DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime P.prime
~~~

or exact equivalent.

Then add one high-level semantic packet theorem if proof-thin:

~~~text
PrimeExponentGauge p
and
g * Ideal.absNorm(cyclotomic ideal) = x^p.
~~~

For example:

~~~text
PrimeAdicFactorPacket.gauge_resolves_to_cyclotomicIdeal
~~~

whose conclusion is a conjunction of the exponent gauge and the already-proved packet ideal equation.

Do not re-prove `gap_mul_cyclotomicIdeal_absNorm_eq_pow`.

## Part F — TraceOne scalar conservation

Connect ValueGauge across the TraceOne scalar bridge.

For a `PrimeTraceOneCoordinatePacket`, expose:

~~~text
valueGaugeCoordinates n
  (Int.natAbs (norm (P.coord (g+u) u)))
=
valueGaugeCoordinates n
  (Ideal.absNorm (cyclotomicLinearFactorIdeal ... g u))
~~~

by rewriting with the existing `TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm` theorem.

If desired, compose Part C and this theorem to expose:

~~~text
valueGaugeCoordinates n TraceOneNorm
  = valueGaugeCoordinates n (GTail p 1 g u).
~~~

Prefer one clean composed theorem over a large family of redundant rewrites.

Important: preserve the existing PR #105 limitation. This is scalar compatibility only. Do not claim equality/isomorphism of the cyclotomic and TraceOne elements or ideals.

## Part G — p = 3, 5, 7 calibration

Add thin fixed-prime calibration packets or theorems that visibly pair:

~~~text
PrimeExponentGauge 3
PrimeExponentGauge 5
PrimeExponentGauge 7
~~~

with the existing dedicated scalar norm equalities.

Preferred shape for each p is a conjunction:

~~~text
PrimeExponentGauge p
and
cyclotomic ideal norm = dedicated TraceOne/Golden scalar norm.
~~~

Reuse directly:

~~~text
cyclotomicIdeal_absNorm_eq_traceOneNorm_three
cyclotomicIdeal_absNorm_eq_traceOneNorm_five
cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
~~~

For p = 5, optionally expose the existing GoldenNorm variant only if it stays one-line. Do not duplicate both p=5 scalar presentations merely for theorem count.

The fixed-prime calibration must not identify the generic TraceOne packet element with the dedicated element; equality of scalar norms is sufficient.

## Part H — public architecture facade

If `DkMath/FLT/Prime.lean` is the established discovery facade, add:

~~~text
import DkMath.FLT.Prime.PrimeGaugeBridge
~~~

Keep `DkMath.NumberTheory.Gauge` free of FLT imports.

## Tests

Create focused tests, preferably:

~~~text
DkMathTest/FLT/Prime/PrimeGaugeBridge.lean
DkMathTest/FLT/Prime/PrimeGaugeBridgeAxiomAudit.lean
~~~

Test at least:

- `PrimeExponentGauge 3`, `5`, `7`;
- a symbolic `GTail = cyclotomic homogeneous evaluation` bridge;
- a generic cyclotomic ideal absNorm = GTail bridge;
- ValueGauge-coordinate preservation across ideal resolution;
- ValueGauge-coordinate preservation across TraceOne scalar transport;
- p = 3/5/7 calibration theorem availability.

Use existing cyclotomic test infrastructure/instances instead of constructing a new number field solely for a trivial example.

## Axiom / safety constraints

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

Run `#print axioms` for every substantive new theorem.

## Forbidden expansion

Do not:

- modify the proofs in GTailCyclotomic, CyclotomicNorm, CyclotomicIdeal, PrimeCyclotomicIdeal, PrimeCyclotomicTraceOne, or PrimeCyclotomicCalibration merely to rename them;
- identify cyclotomic and TraceOne carrier objects;
- prove class-group or unit-sector results;
- implement AdditiveLanding;
- change FLT2;
- prove FLT7 or general FLT;
- introduce a new cyclotomic norm proof.

## Validation

Run focused builds for each changed production/test owner, then at least:

~~~text
lake build DkMath.FLT.Prime.PrimeGaugeBridge
lake build DkMath.FLT.Prime
lake build DkMathTest.FLT.Prime.PrimeGaugeBridge
lake build DkMathTest.FLT.Prime.PrimeGaugeBridgeAxiomAudit
lake build DkMath
git diff --check
~~~

Record the full build job count.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-006.md
~~~

The report must include:

- Outcome A/B;
- exact pinned upstream declarations reused;
- how `PrimeExponentGauge p` supplies primality / `Fact p.Prime`;
- public ExponentGauge -> cyclotomic evaluation theorem;
- public ExponentGauge -> ideal norm theorem;
- ValueGauge conservation theorem(s);
- PrimeAdicFactorPacket integration;
- TraceOne scalar conservation theorem;
- p=3/5/7 calibration API;
- explicit statement that only scalar compatibility is claimed;
- files changed;
- focused/full build results;
- axiom audit;
- forbidden-token scan;
- git diff summary;
- whether GAGE-007 may proceed unchanged.

Preferred Outcome A:

`PrimeExponentGauge p` is now a valid public entry point into the existing prime cyclotomic resolver, the ideal/TraceOne scalar transports preserve the ValueGauge observation, and the p=3/5/7 fixed-prime calibrations are exposed through the same gauge vocabulary.

Stop after GAGE-006. Do not implement GAGE-007.