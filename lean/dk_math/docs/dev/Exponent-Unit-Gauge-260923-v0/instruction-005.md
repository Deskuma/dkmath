# GAGE-005 — FLT2 gauge calibration

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-004.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-004.md
~~~

## Objective

Formalize exponent 2 as the calibration case where the Gap/Beam product can be normalized by the shared gauge 2 and then split into two coprime squares.

This checkpoint is not about proving an impossibility theorem: FLT at exponent 2 has nontrivial solutions. The target is to expose why square landing succeeds.

Use arithmetic only in the production proof. Do not use trigonometry or Euclidean geometry.

Do not shortcut the main gauge mechanism by invoking the final Pythagorean-triple classification theorem.

## Existing assets to reuse

Inspect and reuse:

~~~text
DkMath.NumberTheory.Gauge.Dyadic
DkMath.CosmicFormula.PowerGapBeam
DkMath.CosmicFormula.PowerGapBeamGcd
DkMath.Lib.NumberTheory.PowerFactor
DkMath.CosmicFormula.CosmicFormulaPythagoras
~~~

Also inspect pinned Mathlib parity/gcd lemmas before adding local helpers.

Useful existing theorems include:

~~~text
midpointSquareDifference_eq_increment_beam
flt_eq_forces_powerGapBeam_symm
gcd_powerGap_powerBeam_dvd_d_of_coprime_int
power_factor_split
~~~

and Mathlib's PythagoreanTriple parity/classification results may be used only as test comparators or auxiliary API reconnaissance, not as the production proof of the gauge split.

## Production owner

Create:

~~~text
DkMath/FLT/Two/GaugeCalibration.lean
~~~

with namespace:

~~~lean
namespace DkMath.FLT.Two
~~~

Do not import this module from DkMath.NumberTheory.Gauge.

If repository convention supports a small facade, evaluate:

~~~text
DkMath/FLT/Two.lean
~~~

but do not create unnecessary empty hierarchy files.

## Preferred natural-number calibration domain

Prefer positive natural numbers for the main calibration theorem because the factor split target is:

~~~text
z^2 - y^2 = x^2
(z-y)(z+y) = x^2
~~~

followed by division by 2 and natural-square extraction.

Use integer lemmas only as bridges if they materially simplify gcd/parity reasoning.

## Part A — primitive square-landing packet

Introduce a small structure or predicate only if it simplifies theorem signatures.

Suggested data:

~~~text
x y z : Nat
hx : 0 < x
hy : 0 < y
hz : 0 < z
hEq : x^2 + y^2 = z^2
hcop : Nat.Coprime x y
~~~

Do not store redundant consequences unless they are expensive to rederive.

If a structure would overcomplicate the checkpoint, use theorem arguments directly.

## Part B — primitive parity orientation

Show that exactly one of x,y is even in the primitive positive case, and orient the calibration so the observed side x is even and y is odd.

Preferred approach:

- prove a symmetric orientation theorem;
- or state the main split theorem under explicit assumptions `Even x` and `Odd y`, together with a separate theorem that every primitive positive solution can be swapped into that orientation.

Do not bake an arbitrary orientation into the mathematical meaning.

Also prove z is odd in the oriented primitive case.

Reuse Mathlib parity lemmas wherever possible.

## Part C — Gap/Beam square identity

From:

~~~text
x^2 + y^2 = z^2
~~~

derive:

~~~text
x^2 = (z-y)*(z+y)
~~~

and expose it using the existing PowerGapBeam vocabulary where practical:

~~~text
powerGap y z = z-y
powerBeam 2 y z = z+y
~~~

The theorem should make clear that the square body is:

~~~text
x^2 = Gap * Beam.
~~~

Do not duplicate the generic difference-of-powers proof.

## Part D — exact shared gauge 2

This is the central new theorem of GAGE-005.

Under primitive positive oriented data, prove:

~~~text
Nat.gcd (z-y) (z+y) = 2
~~~

or an equivalent exact statement.

The existing generic PowerGapBeam gcd theorem only gives that the common divisor divides degree 2. GAGE-005 must additionally show both factors are even and hence the gcd is not 1.

The proof should visibly use:

~~~text
y odd
z odd
primitive coprimality
~~~

and should not appeal to the final Pythagorean parametrization.

If proving exact Nat gcd directly is awkward, an equivalent pair of theorems is acceptable:

~~~text
2 divides both Gap and Beam
every common divisor of Gap and Beam divides 2
~~~

plus a final gcd equality corollary.

## Part E — strip the gauge 2

Define or locally name:

~~~text
A := (z-y)/2
B := (z+y)/2
~~~

and prove:

~~~text
z-y = 2*A
z+y = 2*B
Nat.Coprime A B
~~~

Use exact divisibility by 2 from Part D/parity; do not rely on truncating Nat division without proving the corresponding divisibility equalities.

The main conceptual statement is:

~~~text
after removing the entire shared gauge 2, the two remaining carriers are coprime.
~~~

## Part F — normalize the square body

Using x even, set:

~~~text
X := x/2
~~~

and prove:

~~~text
X^2 = A*B
~~~

or the symmetric equality needed by PowerFactor.power_factor_split.

Again, prove the exact `x = 2*X` relation from evenness rather than relying on opaque division simplification.

## Part G — split into squares

Apply:

~~~text
DkMath.Lib.NumberTheory.power_factor_split
~~~

with d = 2 to obtain:

~~~text
exists r, A = r^2
exists s, B = s^2
~~~

Then expose the gauge-normalized endpoint equations:

~~~text
z-y = 2*r^2
z+y = 2*s^2
~~~

This is the minimum required landing calibration.

## Part H — reconstruct the standard arithmetic form

If proof-thin after Part G, derive:

~~~text
x = 2*r*s
y = s^2 - r^2
z = s^2 + r^2
~~~

with suitable ordering / positivity hypotheses on r,s.

This is desirable but not mandatory for Outcome A if Nat subtraction/order bookkeeping becomes disproportionate.

Do not call this a geometric parametrization theorem. In this campaign it is an arithmetic reconstruction from the gauge split.

## Part I — gauge interpretation theorem

Add one high-level theorem or packet whose conclusion visibly packages:

~~~text
shared gauge = 2
stripped carriers are coprime
stripped carriers are squares
~~~

Suggested semantic name:

~~~text
primitiveSquareLandingGaugeSplit
~~~

or equivalent repository-style naming.

This should be the principal public calibration theorem for GAGE-005.

## Part J — comparison with Mathlib classification

Optional test/audit only:

Mathlib.NumberTheory.PythagoreanTriples contains a complete primitive classification.

If useful, add a test showing that the gauge-split output agrees with a standard (3,4,5) or (5,12,13) calibration.

Do not use the classification theorem to replace Parts D-G.

## Concrete calibrations

Test at least:

~~~text
(x,y,z) = (4,3,5)
  Gap = 2
  Beam = 8
  A = 1
  B = 4

(x,y,z) = (12,5,13)
  Gap = 8
  Beam = 18
  A = 4
  B = 9
~~~

These should demonstrate the exact shared gauge 2 and square carriers.

## Relationship to GAGE-004

Document explicitly:

~~~text
GAGE-004: exponent 2 has zero midpoint correction
GAGE-005: primitive square landing factors through an exact shared gauge 2
           and becomes a coprime square product after removing that gauge
~~~

Do not claim that midpoint closure alone proves the factor split.

## Tests and audits

Create focused tests, preferably:

~~~text
DkMathTest/FLT/Two/GaugeCalibration.lean
DkMathTest/FLT/Two/GaugeCalibrationAxiomAudit.lean
~~~

Run #print axioms on every substantive theorem.

## Forbidden expansion

Do not implement:

- GAGE-006 cyclotomic gauge bridge;
- GAGE-007 AdditiveLanding facade;
- general odd-exponent positivity/uniqueness;
- general FLT;
- a new proof of the full Pythagorean classification;
- trigonometric or Euclidean-geometric proof infrastructure.

Do not modify Mathlib-derived classification code.

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

Run focused builds for every changed production/test owner, then at least:

~~~text
lake build DkMath.FLT.Two.GaugeCalibration
lake build DkMathTest.FLT.Two.GaugeCalibration
lake build DkMathTest.FLT.Two.GaugeCalibrationAxiomAudit
lake build DkMath
git diff --check
~~~

If a Two facade is created, build it explicitly.

Record the full build job count.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-005.md
~~~

The report must include:

- Outcome A/B;
- exact production owner and public API;
- primitive parity/orientation route;
- exact shared-gauge-2 proof;
- half-gap / half-beam coprimality proof;
- square-factor split proof and reuse of power_factor_split;
- any reconstructed r,s parametrization;
- GAGE-004 connection;
- concrete 4-3-5 and 12-5-13 calibrations;
- Mathlib Pythagorean-classification usage, if any, explicitly labeled as comparator only;
- files changed;
- focused/full build results;
- axiom audit;
- forbidden-token scan;
- git diff summary;
- whether GAGE-006 may proceed unchanged.

Preferred Outcome A:

Every primitive positive square solution can be oriented so that one side is even, the corresponding Gap and Beam share exactly gauge 2, stripping that gauge yields coprime factors whose product is a square, and each stripped factor is itself a square.

Stop after GAGE-005. Do not implement GAGE-006.