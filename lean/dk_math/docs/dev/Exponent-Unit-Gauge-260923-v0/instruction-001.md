# GAGE-001 — ExponentGauge facade

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-000.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-000.md
~~~

## Objective

Implement only the exponent-side gauge facade.

The mathematical data already exist in PascalPrimeDial / BinomialPrime / BinomialPrimePower. This checkpoint gives that data stable exponent-gauge vocabulary without introducing a second arithmetic implementation.

## Required production module

Create:

~~~text
DkMath/NumberTheory/Gauge/Exponent.lean
~~~

Use namespace:

~~~lean
namespace DkMath.NumberTheory.Gauge
~~~

Import the smallest existing owner set, preferably beginning from:

~~~lean
import DkMath.NumberTheory.PascalPrimeDial
~~~

Only add further imports if a required existing theorem is not already available transitively.

## Public vocabulary

Implement the thinnest definitionally-reducible surface possible.

Preferred shapes:

~~~lean
abbrev exponentGaugeHeight (p n k : ℕ) : ℕ :=
  pascalPrimeDialHeight p n k

abbrev PrimeExponentGauge (p : ℕ) : Prop :=
  InnerRowSupportPrime p p

abbrev PrimePowerExponentGauge (p e : ℕ) : Prop :=
  PrimePowerRowSupport p e
~~~

If Lean naming or import constraints suggest an even thinner equivalent shape, document the adjustment in report-001.md. Do not replace these aliases with a new record or structure.

## Required theorem facade

Expose thin semantic bridge theorems corresponding to all of the following facts.

### A. Prime row support

For prime p:

~~~text
PrimeExponentGauge p
~~~

must follow directly from the existing prime-row support theorem.

### B. Prime row exact height

For prime p:

~~~text
UniformPrimeDialHeight p p 1
~~~

and/or the equivalent statement under exponentGaugeHeight vocabulary.

Do not duplicate the existing proof of prime_uniformPrimeDialHeight_self.

### C. Pre-birth zero height

For prime p and n < p:

~~~text
exponentGaugeHeight p n k = 0
~~~

as a semantic wrapper over pascalPrimeDialHeight_eq_zero_of_row_lt.

### D. Prime-power support

For prime p and positive e:

~~~text
PrimePowerExponentGauge p e
~~~

using the existing PrimePowerRowSupport theorem.

### E. Exact prime-power depth formula

For prime p, k <= p^e, k != 0:

~~~text
exponentGaugeHeight p (p^e) k + padicValNat p k = e
~~~

or an equivalent subtractive theorem, directly reusing the existing Kummer/binomial valuation theorem.

### F. Unit-index full depth

For prime p, positive inner k < p^e, and not p | k:

~~~text
exponentGaugeHeight p (p^e) k = e
~~~

This should be obtained from prime_power_unitFilteredPrimeDialHeight or the exact height formula. Prefer the shortest existing route.

## Semantic constraints

1. exponentGaugeHeight must be definitionally the same observation as pascalPrimeDialHeight.
2. PrimeExponentGauge must not silently mean StructuralArithmetic.SamePowerSector.
3. PrimePowerExponentGauge must not assert any converse characterization not already proved.
4. Preserve the distinction:

    ~~~text
    support prime          = divisibility support
    prime-dial height      = p-adic valuation depth
    filtered unit indices  = indices with p not dividing k
    ~~~

5. No ValueGauge or mod-exponent value residue in this checkpoint.
6. No new structure, class, quotient, or custom valuation engine.
7. No theorem may depend on FLT modules.

## Facade integration

Evaluate and implement the smallest clean public import surface.

Preferred if consistent with repository conventions:

~~~text
DkMath/NumberTheory/Gauge.lean
  imports DkMath.NumberTheory.Gauge.Exponent
~~~

If this facade is created, add the corresponding public import to DkMath.lean in the same style as neighboring NumberTheory modules.

Do not add empty placeholder imports for future Value/Dyadic/Landing modules.

## Tests and audits

Create focused tests under DkMathTest, preferably:

~~~text
DkMathTest/NumberTheory/Gauge/Exponent.lean
DkMathTest/NumberTheory/Gauge/ExponentAxiomAudit.lean
~~~

The API test should #check the public aliases/theorems and include a few tiny compile-time examples for prime 3 or 5 if useful.

The axiom audit must #print axioms for every new substantive theorem. Abbrevs do not need artificial proof wrappers solely for auditing.

Expected allowed axioms are only the normal Lean/Mathlib logical foundations already present in the reused upstream theorems. Record the actual output in the report.

## Forbidden work

Do not implement or modify:

~~~text
Gauge.Value
Gauge.Dyadic
Gauge.Landing
DkMath.FLT.QuadraticGauge
DkMath.FLT.Prime.PrimeGaugeBridge
~~~

Do not edit PascalPrimeDial, BinomialPrime, or BinomialPrimePower merely to rename their APIs. The new module is a facade.

Do not attempt the converse:

~~~text
common inner support prime -> row is a prime power
~~~

That belongs to GAGE-002.

## Validation

Run at least:

~~~text
lake build DkMath.NumberTheory.Gauge.Exponent
lake build DkMathTest.NumberTheory.Gauge.Exponent
lake build DkMathTest.NumberTheory.Gauge.ExponentAxiomAudit
~~~

If a Gauge facade or DkMath.lean is changed, build those owners too.

Then run:

~~~text
lake build DkMath
git diff --check
~~~

Scan the changed production/test files for:

~~~text
sorry
admit
sorryAx
axiom
unsafe
~~~

Do not count comments/docstrings when interpreting a textual scan; report any genuine declaration hits explicitly.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-001.md
~~~

The report must include:

- Outcome A/B;
- exact public API added;
- proof/reuse mapping from every new theorem to its upstream owner theorem;
- confirmation that StructuralArithmetic.PowerGauge and MultiGauge were not conflated with this facade;
- files changed;
- focused build results;
- full DkMath build result;
- axiom audit results;
- forbidden-token scan result;
- git diff summary;
- any issue that should change GAGE-002 scope.

Preferred Outcome A:

A thin, no-duplication exponent gauge facade compiles and is publicly importable.

Stop after GAGE-001. Do not implement GAGE-002.
