# GAGE-000 — Inventory and API boundary

You are implementing checkpoint GAGE-000 on branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
~~~

## Objective

Do not start by inventing a large Gauge hierarchy. First determine exactly how much of the intended exponent/unit-gauge framework already exists in production DkMath, and freeze the smallest non-duplicating API boundary for the next checkpoint.

This is an implementation-audit checkpoint. Its output is a reviewed design and, only if justified, a very small facade/scaffold. Do not move heavy mathematics or rename existing production APIs.

## Required inventory

Inspect at least:

~~~text
DkMath.NumberTheory.BinomialPrime
DkMath.NumberTheory.BinomialPrimePower
DkMath.NumberTheory.PascalPrimeDial
DkMath.NumberTheory.WeightedBinomial
DkMath.NumberTheory.WeightedGNBridge
DkMath.CosmicFormula.PowerGapBeam
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailCyclotomic
DkMath.CFBRC.CyclotomicNorm
DkMath.CFBRC.CyclotomicIdeal
DkMath.FLT.Prime.PrimeCyclotomicIdeal
DkMath.FLT.Prime.PrimeCyclotomicTraceOne
DkMath.FLT.Prime.PrimeCyclotomicCalibration
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership
~~~

Also search for existing APIs for:

- p-adic height of binomial coefficients;
- prime / prime-power row support;
- n-th-power factor extraction;
- product-of-coprime factors equals a power;
- d = 2 Gap/Beam specialization;
- parity / gcd facts useful for primitive FLT2;
- generic power landing predicates or criteria.

## Required analysis

Create an explicit table with columns:

~~~text
concept
existing owner/module
existing theorem/definition names
reuse status
missing theorem if any
proposed new owner
~~~

Include at least:

~~~text
ExponentGaugeHeight
PrimeExponentGauge
PrimePowerExponentGauge
ValueGauge / local power residue
DyadicGauge
MidpointCorrection
FLT2 gauge split
CyclotomicGaugeResolver
GaugeConservationKernel
AdditiveLanding
~~~

## Architectural constraints

1. Keep exponent-side and value-side gauge data distinct.
2. Do not duplicate pascalPrimeDialHeight under a new implementation if a semantic alias or theorem is enough.
3. Do not duplicate PR #105 cyclotomic/Norm/ideal/TraceOne proofs.
4. Do not move FLT-specific theorems into a generic library without a genuinely generic statement.
5. Do not introduce quotient-group machinery in this checkpoint.
6. Do not claim that the gauge vocabulary itself proves FLT.
7. No sorry, admit, sorryAx, declared axiom, or unsafe proof shortcut.

## Production change policy

Outcome A: inventory identifies a clean minimal production surface. Add only the smallest justified scaffold and prepare GAGE-001.

Outcome B: no production code is needed yet. Record the exact proposed file/API layout and unresolved mathematical/API choices.

Do not force Outcome A.

## Suggested file layout to evaluate

~~~text
DkMath/NumberTheory/Gauge.lean
DkMath/NumberTheory/Gauge/Exponent.lean
DkMath/NumberTheory/Gauge/Value.lean
DkMath/NumberTheory/Gauge/Dyadic.lean
DkMath/NumberTheory/Gauge/Landing.lean
DkMath/FLT/Prime/PrimeGaugeBridge.lean
~~~

A thinner layout is preferred if existing ownership makes these redundant.

## Validation

If production Lean files are changed, run focused builds for each changed module and facade, then:

~~~text
lake build DkMath
git diff --check
~~~

Run #print axioms on every new substantive theorem.

If only documentation is changed, record that no Lean build was necessary.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-000.md
~~~

The report must contain:

- Outcome A or B;
- exact inventory table;
- recommended module/file layout;
- APIs to reuse unchanged;
- genuinely missing lemmas;
- proposed scope for GAGE-001;
- build / audit results;
- git diff summary.

Stop after GAGE-000. Do not implement GAGE-001.
