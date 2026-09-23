# GAGE-003 — ValueGauge / local power residue

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-002.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-002.md
~~~

## Objective

Implement the value-side gauge separately from the completed exponent-side Pascal gauge.

The intended mathematical object is the local residue:

~~~text
v_p(a) mod n
~~~

and the full prime-coordinate vector:

~~~text
p |-> v_p(a) mod n.
~~~

Do not implement a second modulo/projection engine. The existing StructuralArithmetic modules already provide exactly this mechanism.

## Existing implementation to reuse

Inspect and reuse:

~~~text
DkMath.NumberTheory.StructuralArithmetic.PowerGauge
DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
DkMath.Lib.NumberTheory.PadicValNat
~~~

Especially:

~~~text
projectExponent
PrimeIndex
primeExponentCoordinates
projectPrimeCoordinates
padicValNat_mul_pow
projectPrimeCoordinates_mul_pow
samePowerStructure_primeCoordinates_mul_pow
projectPrimeCoordinates_period_zero
projectPrimeCoordinates_period_one
~~~

## Required production module

Create:

~~~text
DkMath/NumberTheory/Gauge/Value.lean
~~~

and add it to:

~~~text
DkMath/NumberTheory/Gauge.lean
~~~

Do not add any FLT import.

Use namespace:

~~~lean
namespace DkMath.NumberTheory.Gauge
~~~

## Part A — thin value-side vocabulary

Preferred semantic surface:

~~~lean
abbrev ValueGaugePrime := DkMath.NumberTheory.StructuralArithmetic.PrimeIndex

abbrev valueGaugeResidue
    (n : ℕ) (p : ValueGaugePrime) (a : ℕ) : ℕ :=
  DkMath.NumberTheory.StructuralArithmetic.projectExponent
    n (padicValNat p.1 a)

abbrev valueGaugeCoordinates (n a : ℕ) : ValueGaugePrime → ℕ :=
  DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates n a
~~~

Exact names may be adjusted to repository style, but the definitions must be definitionally thin over the existing owners.

Do not call this ExponentGauge. This is the value-side gauge.

## Part B — exact bridge theorems

Expose theorem-level equalities showing the intended meaning.

At minimum:

### B1. residue is valuation modulo exponent

~~~text
valueGaugeResidue n p a = padicValNat p a % n
~~~

### B2. coordinate application

~~~text
valueGaugeCoordinates n a p = valueGaugeResidue n p a
~~~

These should be rfl/simp-level bridges if the abbreviations are chosen correctly.

## Part C — power landing gives zero local residue

For prime coordinate p and nonzero base a, prove:

~~~text
valueGaugeResidue n p (a^n) = 0
~~~

Reuse:

~~~text
DkMath.Lib.NumberTheory.padicValNat_pow
projectExponent_period_mul
~~~

or the shortest equivalent existing route.

Do not re-prove valuation-of-power arithmetic.

Then expose the vector form:

~~~text
valueGaugeCoordinates n (a^n) = fun _ => 0
~~~

for nonzero a.

## Part D — multiplication by an n-th power is invisible

Expose a semantic wrapper over the existing StructuralArithmetic theorem:

~~~text
valueGaugeCoordinates n (a * b^n)
  = valueGaugeCoordinates n a
~~~

under the nonzero hypotheses required by the existing theorem.

This is a central conservation law for the value gauge.

Do not duplicate the proof of projectPrimeCoordinates_mul_pow.

## Part E — positive/nonzero purity predicate

Introduce a small predicate that avoids silently treating padicValNat's zero convention as ordinary factorization data.

Preferred shape:

~~~lean
def ValueGaugePure (n a : ℕ) : Prop :=
  a ≠ 0 ∧ valueGaugeCoordinates n a = fun _ => 0
~~~

or an equivalent forall-prime pointwise form if it is easier to use.

The explicit a ≠ 0 condition is intentional.

Then prove:

~~~text
a != 0 -> ValueGaugePure n (a^n)
~~~

Again, this is only the forward perfect-power direction.

## Part F — optional converse reconnaissance

Investigate whether the pinned Mathlib version already has a short theorem equivalent to:

~~~text
a != 0
all prime valuations of a are divisible by n
-------------------------------------------
exists b, a = b^n
~~~

If an existing theorem closes this with a thin wrapper, you may expose it.

If not, do NOT build a new factorization reconstruction proof in GAGE-003. Record it as deferred work in report-003.md.

The v0 success criterion does not require this converse.

## Boundary behavior

Explicitly document/test:

~~~text
n = 0
n = 1
a = 0
a = 1
~~~

Important:

- projectExponent 0 v = v;
- projectExponent 1 v = 0;
- padicValNat has a conventional value at 0, so ValueGaugePure must not silently identify zero with ordinary nonzero power-factor data.

Do not make false statements about zero.

## Calibration examples

Include small tests illustrating the semantics, for example:

~~~text
36 is square-gauge pure
72 is not square-gauge pure at p = 2
27 is cube-gauge pure
multiplying a nonzero value by 5^3 does not change its period-3 value gauge
~~~

Use theorem-driven tests where possible. Small norm_num checks may be used only for calibration.

## Relationship to StructuralArithmetic

The report must explicitly state:

~~~text
ExponentGauge (Pascal side) != StructuralArithmetic.PowerGauge
ValueGauge (value side) is a semantic facade over StructuralArithmetic prime-coordinate projection
~~~

This explicit bridge resolves the naming distinction discovered in GAGE-000.

Do not rename or move the existing StructuralArithmetic files.

## Tests and audits

Create:

~~~text
DkMathTest/NumberTheory/Gauge/Value.lean
DkMathTest/NumberTheory/Gauge/ValueAxiomAudit.lean
~~~

and update the Gauge facade tests only if repository convention requires it.

Run #print axioms for every new substantive theorem.

## Forbidden expansion

Do not implement:

- DyadicGauge / midpoint correction;
- FLT2 calibration;
- CyclotomicGaugeBridge;
- AdditiveLanding;
- quotient K*/(K*)^n machinery;
- a new valuation implementation;
- any general FLT statement.

## Safety constraints

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

## Validation

Run at least:

~~~text
lake build DkMath.NumberTheory.Gauge.Value
lake build DkMath.NumberTheory.Gauge
lake build DkMathTest.NumberTheory.Gauge.Value
lake build DkMathTest.NumberTheory.Gauge.ValueAxiomAudit
lake build DkMath
git diff --check
~~~

Record the full build job count.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-003.md
~~~

The report must include:

- Outcome A/B;
- exact existing StructuralArithmetic APIs reused;
- exact ValueGauge public API added;
- proof/reuse map for every substantive theorem;
- treatment of n = 0, n = 1, a = 0;
- purity predicate design;
- result of optional converse reconnaissance;
- calibration examples;
- files changed;
- focused/full build results;
- axiom audit;
- forbidden-token scan;
- git diff summary;
- whether GAGE-004 may proceed unchanged.

Preferred Outcome A:

The value-side gauge is publicly available as the prime-valuation residue vector modulo n, exact n-th powers land in the zero sector, and multiplication by an n-th power preserves the gauge observation.

Stop after GAGE-003. Do not implement GAGE-004.