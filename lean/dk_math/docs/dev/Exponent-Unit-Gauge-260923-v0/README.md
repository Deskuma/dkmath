# Exponent Unit Gauge

Branch: research/Exponent-Unit-Gauge-260923-v0

Base: develop

## Mission

This campaign extracts the exponent/unit-gauge mechanism that has so far been used only indirectly across DkMath FLT work.

The project already has strong implementations for:

- Pascal/binomial prime support and p-adic beam height;
- weighted binomial and one-gap GTail/GN transport;
- generic power Gap/Beam factorization;
- TraceOne arbitrary-power landing criteria;
- the PR #105 GTail -> cyclotomic -> Norm -> ideal -> valuation -> TraceOne conservation chain;
- fixed-prime calibrations at p = 3, 5, 7.

The missing layer is a common vocabulary and theorem surface that treats the exponent itself as structured data rather than as only a natural-number parameter.

Intended chain:

~~~text
exponent n
    |
    v
Pascal / prime-dial extraction
    |
    v
ExponentGauge
    |
    +--------------------+
    |                    |
    v                    v
2-gauge / midpoint      prime p gauge
calibration             cyclotomic carrier
    |                    |
    v                    v
FLT2 landing        GN = Phi_p = Norm = ideal norm
                         |
                         v
                    TraceOne / valuation
                         |
                         v
                    additive landing
~~~

## Core distinction

Keep distinct:

~~~text
base/content value
unit scale
growth/exponent depth
prime support of the exponent
value-side p-adic spectrum
exponent-side Pascal p-adic spectrum
resolved algebraic carrier
landing / non-landing condition
~~~

In particular, do not conflate ValueGauge n x, which measures value-side n-th-power landing, with ExponentGauge n, which extracts structure carried by the exponent itself.

## Existing foundations

Reuse, do not duplicate:

~~~text
DkMath.NumberTheory.BinomialPrime
DkMath.NumberTheory.BinomialPrimePower
DkMath.NumberTheory.PascalPrimeDial
DkMath.NumberTheory.WeightedBinomial
DkMath.NumberTheory.WeightedGNBridge
DkMath.CosmicFormula.PowerGapBeam
DkMath.Lib.Cosmic.GTailCyclotomic
DkMath.CFBRC.CyclotomicNorm
DkMath.CFBRC.CyclotomicIdeal
DkMath.FLT.Prime.PrimeCyclotomicIdeal
DkMath.FLT.Prime.PrimeCyclotomicTraceOne
DkMath.FLT.Prime.PrimeCyclotomicCalibration
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership
~~~

## Mathematical calibration targets

### Exponent 2

First calibration:

~~~text
(x + u)^2 - x^2 = 2*u*(x + u/2)
~~~

Prefer a denominator-free production form in Lean. The intended interpretation is that exponent 2 is the nonlinear exponent for which the midpoint correction vanishes exactly.

Also connect the existing d = 2 PowerGapBeam factorization to a primitive FLT2 arithmetic calibration without trigonometry or Euclidean geometry as proof infrastructure.

### Prime exponents

For prime p, the target bridge is already largely implemented:

~~~text
GTail p 1 x u
  = GTailCyclotomicShell p x u
  = GN p x u
  = homogeneous Phi_p carrier
  = cyclotomic field norm
  = principal-ideal absNorm
  = TraceOne scalar norm
~~~

The new gauge layer should expose this as a semantic theorem family rather than re-prove the algebra.

## Non-goals for v0

- no proof of general FLT;
- no terminal FLT7 contradiction;
- no new class-group theorem;
- no replacement for PR #105;
- no quotient-group-heavy power-class formalization unless clearly justified;
- no claim that every dyadic refinement point is prime;
- no identification of geometric dimension with exponent depth.

## Completion criterion

v0 is complete when DkMath has a coherent public theorem surface in which:

1. Pascal prime-dial data are exposed as exponent-gauge data;
2. value-side n-th-power gauge residue is separated from exponent-gauge data;
3. exponent 2 has an exact midpoint/dyadic calibration;
4. FLT2 has a gauge-only arithmetic calibration;
5. prime p gauge data connect by named bridges to the PR #105 cyclotomic/Norm/ideal/TraceOne conservation chain;
6. additive landing has a neutral common API with fixed-prime calibrations;
7. no general-FLT theorem is claimed unless independently proved.

See ROADMAP.md for checkpoints.