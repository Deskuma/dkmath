# GAGE-007 — AdditiveLanding facade and v0 closure

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-006.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-006.md
~~~

## Objective

Close v0 with a small neutral landing vocabulary that can describe:

1. ordinary n-th-power image landing;
2. beta-times-n-th-power/Core-image landing;
3. additive landing x^n + y^n = z^n;
4. positive-natural additive landing;
5. the ValueGauge necessary condition for power landing;
6. the existing TraceOne arbitrary-power receiver;
7. fixed-exponent calibration at n = 2, 3, 5;
8. the explicit unresolved status at n = 7.

This checkpoint must not prove new FLT mathematics.

## Part A — neutral production owner

Create:

~~~text
DkMath/NumberTheory/Gauge/Landing.lean
~~~

and import it from:

~~~text
DkMath/NumberTheory/Gauge.lean
~~~

Use namespace:

~~~lean
namespace DkMath.NumberTheory.Gauge
~~~

Prefer imports beginning from:

~~~text
DkMath.NumberTheory.Gauge.Value
~~~

Only import TraceOnePowerLanding into this module if the resulting dependency remains reasonably neutral. If that makes the generic Gauge facade unnecessarily heavy, create a small separate neutral adapter module and document the choice.

Do not import any FLT module into DkMath.NumberTheory.Gauge.

## Part B — neutral landing predicates

Add thin definitions with the weakest practical algebraic assumptions.

Preferred shapes:

~~~lean
def PowerLanding {R : Type*} [Monoid R] (n : ℕ) (a : R) : Prop :=
  ∃ b : R, a = b ^ n

def CorePowerLanding {R : Type*} [Monoid R]
    (n : ℕ) (alpha beta : R) : Prop :=
  ∃ gamma : R, alpha = beta * gamma ^ n

def AdditiveLanding (n x y : ℕ) : Prop :=
  ∃ z : ℕ, x ^ n + y ^ n = z ^ n

def PositiveAdditiveLanding (n x y : ℕ) : Prop :=
  ∃ z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x ^ n + y ^ n = z ^ n
~~~

Equivalent argument order/naming is acceptable if it improves Lean ergonomics.

Do not bake primality into AdditiveLanding. Landing is a neutral concept for every exponent.

## Part C — basic neutral bridges

Prove only proof-thin facts, for example:

~~~text
PowerLanding n a -> exists b, a = b^n
CorePowerLanding n alpha beta -> exists gamma, alpha = beta*gamma^n
PositiveAdditiveLanding n x y -> AdditiveLanding n x y
~~~

These may simply be eliminator/constructor lemmas if they improve use sites. Do not add theorem-count padding.

## Part D — ValueGauge necessary condition

For natural values, expose the essential necessary condition:

~~~text
a != 0
PowerLanding n a
----------------
ValueGaugePure n a
~~~

Proof route:

1. obtain `a = b^n`;
2. derive `b != 0` from `a != 0`;
3. reuse `valueGaugePure_pow` or the exact existing GAGE-003 theorem.

Do not prove the converse perfect-power reconstruction here.

Also prove the additive consequence:

~~~text
PositiveAdditiveLanding n x y
  -> ValueGaugePure n (x^n + y^n)
~~~

by rewriting the landed sum to `z^n` and using z > 0.

This theorem formalizes:

~~~text
additive landing => zero ValueGauge defect
~~~

as a necessary condition only.

Do not claim:

~~~text
zero ValueGauge defect => additive landing
~~~

unless an existing theorem directly proves it, which is not expected in v0.

## Part E — TraceOne CorePowerLanding adapter

Reuse:

~~~text
DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff
~~~

to expose the existing receiver through the new neutral predicate.

Preferred theorem shape:

~~~text
CorePowerLanding r alpha beta
  iff
the existing pair of TraceOne coordinate equations
~~~

under `norm beta != 0`.

This must be a wrapper/adaptation of the existing theorem, not a reproof of the coordinate reconstruction.

If importing TraceOnePowerLanding into the generic Landing module is architecturally undesirable, place this adapter in a separate neutral file such as:

~~~text
DkMath/NumberTheory/Gauge/TraceOneLanding.lean
~~~

and import it from Gauge.lean only if the public-facade cost is acceptable.

Record the ownership decision in report-007.md.

## Part F — FLT-specific calibration owner

Create a separate FLT-side calibration module, preferred:

~~~text
DkMath/FLT/GaugeLandingCalibration.lean
~~~

or an equivalently clear owner.

This module may import:

~~~text
DkMath.NumberTheory.Gauge.Landing
DkMath.FLT.Two.GaugeCalibration
DkMath.FLT.Three
DkMath.FLT.Five
DkMath.FLT.Prime.PrimeGaugeBridge
~~~

Do not import this calibration module back into DkMath.NumberTheory.Gauge.

Do not add it to the historical broad DkMath.FLT aggregator unless repository convention clearly requires that. Prefer explicit discovery if uncertain.

## Part G — exponent 2 landing calibration

Expose exponent 2 as a landing case, not a non-landing theorem.

At minimum prove one generic bridge from an existing primitive square solution:

~~~text
PrimitiveSquareSolution P
  -> PositiveAdditiveLanding 2 P.x P.y
~~~

or the equivalent theorem using the stored positivity/equation fields.

Then connect the stronger GAGE-005 result:

~~~text
PrimitiveSquareSolution
  -> oriented PrimitiveSquareLandingGaugeSplit
~~~

to the landing vocabulary in one theorem/conjunction if useful.

Do not re-prove the gauge split.

Concrete `(3,4,5)` or `(4,3,5)` landing should be tested.

## Part H — exponent 3 non-landing calibration

Using:

~~~text
DkMath.FLT.Three.fermatThree_no_positive_solution
~~~

prove a thin wrapper:

~~~text
forall x y, not PositiveAdditiveLanding 3 x y
~~~

or an equivalent three-variable no-landing theorem expressed in the new vocabulary.

The proof should be only unpacking the landing witness and applying the existing endpoint.

Do not reopen the FLT3 proof tower.

## Part I — exponent 5 non-landing calibration

Using:

~~~text
DkMath.FLT.Five.fermatFive_no_positive_solution
~~~

prove the analogous wrapper:

~~~text
forall x y, not PositiveAdditiveLanding 5 x y.
~~~

Again, do not re-prove any FLT5 arithmetic.

Check the exact existing `Fermat5Equation` reducibility/signature and use simp/unfold only as required.

## Part J — exponent 7 boundary

Do NOT add:

~~~text
not PositiveAdditiveLanding 7 x y
~~~

unless a completed unconditional public FLT7 theorem is independently present and verified on this branch.

Current campaign expectation is that no such terminal theorem is available.

Instead, expose only what is already justified, if a useful theorem is proof-thin:

~~~text
PrimeExponentGauge 7
and/or
the existing p=7 cyclotomic/TraceOne scalar calibration.
~~~

Do not disguise this as additive non-landing.

`report-007.md` must explicitly state:

~~~text
p=7 exponent-gauge resolution is implemented;
terminal positive additive non-landing is not claimed by this campaign.
~~~

## Part K — final v0 semantic summary theorem surface

Do not create a giant structure containing all checkpoints.

Instead ensure the public API can express these four statements directly:

~~~text
1. prime exponent support is detected by Pascal structure;
2. exact n-th powers have zero ValueGauge defect;
3. exponent 2 admits positive additive landing and exact gauge-2 splitting;
4. exponents 3 and 5 have no positive additive landing, by existing completed endpoints;
5. odd-prime PrimeExponentGauge resolves to the cyclotomic/TraceOne scalar chain.
~~~

These statements need not be combined into one theorem.

## Part L — tests

Create focused neutral tests:

~~~text
DkMathTest/NumberTheory/Gauge/Landing.lean
DkMathTest/NumberTheory/Gauge/LandingAxiomAudit.lean
~~~

and FLT calibration tests, preferably:

~~~text
DkMathTest/FLT/GaugeLandingCalibration.lean
DkMathTest/FLT/GaugeLandingCalibrationAxiomAudit.lean
~~~

Test at least:

- `PowerLanding 2 36` and its ValueGauge purity;
- positive additive landing `3^2 + 4^2 = 5^2`;
- no PositiveAdditiveLanding at exponent 3;
- no PositiveAdditiveLanding at exponent 5;
- TraceOne CorePowerLanding wrapper compiles, if added;
- p=7 is represented only by its existing gauge/resolver calibration, not no-landing.

## Part M — documentation closure

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-007.md
~~~

After successful implementation/builds, update ROADMAP.md status to indicate that GAGE-000 through GAGE-007 have been executed. Do not write `v0 COMPLETE` if report-007 concludes Outcome B or identifies a blocking API gap.

Do not rewrite historical reports.

## Axiom / safety constraints

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

Run #print axioms on every substantive new theorem.

## Forbidden expansion

Do not:

- prove the ValueGauge perfect-power converse;
- prove new FLT3/FLT5 mathematics;
- claim FLT7 unconditionality;
- claim general FLT;
- modify the internals of the completed FLT3/FLT5 proof towers;
- modify GAGE-005 square split merely to fit naming;
- identify cyclotomic and TraceOne carriers;
- add class-group/unit-sector results;
- build a quotient K*/(K*)^n API.

## Validation

Run focused builds for every changed owner, then at least:

~~~text
lake build DkMath.NumberTheory.Gauge.Landing
lake build DkMath.NumberTheory.Gauge
lake build DkMathTest.NumberTheory.Gauge.Landing
lake build DkMathTest.NumberTheory.Gauge.LandingAxiomAudit
lake build DkMath.FLT.GaugeLandingCalibration
lake build DkMathTest.FLT.GaugeLandingCalibration
lake build DkMathTest.FLT.GaugeLandingCalibrationAxiomAudit
lake build DkMath
git diff --check
~~~

Adjust exact module build names only if the ownership decision differs and record that decision.

Record the full build job count.

## Deliverable report

`report-007.md` must include:

- Outcome A/B;
- exact neutral landing definitions added;
- ValueGauge necessary-condition theorem(s);
- TraceOne CorePowerLanding adapter and ownership decision;
- FLT2 positive landing calibration;
- FLT3 no-positive-landing wrapper;
- FLT5 no-positive-landing wrapper;
- explicit p=7 unresolved additive-landing boundary;
- relationship to PrimeGaugeBridge;
- public import/facade changes;
- files changed;
- focused/full build results;
- axiom audits;
- forbidden-token scan;
- git diff summary;
- final v0 completion assessment;
- remaining deferred research list.

Preferred Outcome A:

The v0 framework now has a neutral landing vocabulary, power landing implies zero ValueGauge defect, TraceOne power/Core-image landing is exposed through that vocabulary, exponent 2 is calibrated as positive square landing, exponents 3 and 5 are calibrated as positive additive non-landing using their existing completed endpoints, and exponent 7 is honestly left at the resolver boundary.

Stop after GAGE-007. Do not begin any post-v0 research campaign.