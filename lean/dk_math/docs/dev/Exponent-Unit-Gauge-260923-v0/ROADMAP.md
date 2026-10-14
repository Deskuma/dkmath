# ROADMAP — Exponent Unit Gauge v0

Status: GAGE-000 through GAGE-007 executed; v0 closure recorded in report-007.md

Branch: research/Exponent-Unit-Gauge-260923-v0

## Design rule

Each checkpoint must first search for reusable production APIs. Prefer thin semantic bridges over duplicate arithmetic. New abstractions must preserve existing theorem ownership.

## GAGE-000 — Inventory and API boundary

Goal: determine the exact production surface to reuse and freeze the first public vocabulary.

Deliverables:

- inventory of Pascal/exponent, value/power, Gap/Beam, cyclotomic, Norm/ideal/valuation, TraceOne, and landing APIs;
- classify each as reuse as-is, semantic alias/bridge, genuinely missing theorem, or deferred research;
- propose module/file ownership;
- no speculative general-FLT theorem;
- report-000.md with Outcome A/B.

## GAGE-001 — ExponentGauge facade

Promote existing Pascal prime-dial facts into explicit exponent-gauge vocabulary.

Expected reuse:

~~~text
pascalPrimeDialHeight
UniformPrimeDialHeight
FilteredPrimeDialHeight
PrimePowerRowSupport
padicValNat_choose_prime_pow
~~~

Keep this layer thin.

## GAGE-002 — Prime-power purity / detector

Establish the strongest practical characterization supported by the existing binomial API.

Desired direction:

~~~text
prime row       -> primitive exponent gauge
prime-power row -> same primitive support prime with depth
~~~

Investigate, but do not assume without proof, converse characterizations such as a common inner-row support prime forcing a prime-power row.

## GAGE-003 — ValueGauge / power residue

Introduce the value-side gauge separately from ExponentGauge.

Prefer an elementary valuation interface first:

~~~text
powerGaugeResidue n p a := padicValNat p a % n
~~~

Target n-th powers having zero local residue, multiplicative transport where valid, and a clean positive-integer purity predicate. Avoid quotient groups in v0 unless clearly cheaper.

## GAGE-004 — DyadicGauge / midpoint correction

Formalize the exponent-2 calibration. Prefer a denominator-free scaled identity equivalent to the midpoint correction formula.

Targets:

- exact d = 2 correction-zero theorem;
- explicit d = 3 correction formula;
- generic odd-correction expansion if technically clean;
- positivity/nonzero results only if small enough for v0.

## GAGE-005 — FLT2 gauge calibration

Use arithmetic only and reuse DkMath.CosmicFormula.PowerGapBeam.

Target chain:

~~~text
z^2 - y^2 = x^2
(z-y)(z+y) = x^2
common boundary gauge = 2
strip the common 2
coprime product is a square
each stripped factor is a square
~~~

## GAGE-006 — Cyclotomic gauge bridge

Add semantic bridges from ExponentGauge to the already-proved PR #105 conservation chain. Do not re-prove GN = shell = Norm = ideal norm = TraceOne scalar norm. Calibrate p = 3, 5, 7 with existing production theorems.

## GAGE-007 — AdditiveLanding facade

Introduce a neutral landing vocabulary for n-th-power landing, additive landing of x^n + y^n, and resolved carrier landing. Connect existing fixed-prime theorems where available. Do not prove general non-landing for all p > 2 here.

## Deferred research after v0

- universal additive-landing obstruction for all prime exponents;
- general-FLT terminal contradiction;
- class-group elimination for arbitrary p;
- complete abstract quotient K*/(K*)^n API;
- analytic interpretations of dyadic refinement.

These become a new campaign only after v0 exposes the exact remaining Gap.
