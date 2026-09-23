# GAGE-004 — DyadicGauge / midpoint correction

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-003.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-003.md
~~~

## Objective

Formalize the exponent-2 midpoint calibration that motivated the dyadic/half-unit gauge interpretation.

The production core must avoid division by 2. Use a scaled midpoint defect with integer coefficients, then derive the familiar half-unit identity as a field/real corollary.

Do not implement FLT2 yet. GAGE-004 is only the local exponent/midpoint mechanism.

## Existing assets to inspect and reuse

Inspect:

~~~text
DkMath.CosmicFormula.PowerGapBeam
DkMath.CosmicFormula.HalfUnitZeroConjugate
DkMath.Algebra.DiffPow
~~~

Also search Mathlib for any existing centered-binomial or symmetric-difference theorem before implementing a generic expansion.

Do not duplicate:

~~~text
powerGap
powerBeam
pow_sub_pow_eq_gap_mul_powerBeam
powerBeam_two
powerBeam_three
powerBeam_four
HalfUnitZeroConjugate.halfUnit
~~~

unless a new theorem is genuinely a semantic bridge.

## Required production module

Create:

~~~text
DkMath/NumberTheory/Gauge/Dyadic.lean
~~~

and import it from:

~~~text
DkMath/NumberTheory/Gauge.lean
~~~

Use namespace:

~~~lean
namespace DkMath.NumberTheory.Gauge
~~~

## Part A — denominator-free midpoint defect

Introduce the thinnest useful definition.

Preferred generic shape:

~~~lean
def scaledMidpointDefect
    {R : Type*} [CommRing R]
    (d : ℕ) (x u : R) : R :=
  (2 : R) ^ (d - 1) * ((x + u) ^ d - x ^ d)
    - (d : R) * u * (2 * x + u) ^ (d - 1)
~~~

Exact syntax may be adjusted for Lean casts and multiplication order.

The definition must stay pre-geometric: it measures failure of the endpoint power difference to be represented solely by the midpoint main term.

## Part B — exact low-degree calibration

Prove at minimum:

~~~text
scaledMidpointDefect 2 x u = 0
scaledMidpointDefect 3 x u = u^3
scaledMidpointDefect 4 x u = 4*u^3*(2*x+u)
~~~

over the weakest practical commutative-ring assumptions.

Prefer `ring` after unfolding the definition. Do not manually expand powers unless required.

These are the primary v0 calibration theorems.

## Part C — exponent-2 half-unit identity

Expose the unscaled midpoint identity over a suitable characteristic-zero field or linear ordered field.

Target semantic statement:

~~~text
(x + u)^2 - x^2
  = 2 * u * (x + u / 2)
~~~

Use a generic field if straightforward. Otherwise use ℚ or ℝ, but document why.

If using an existing real half-unit definition is semantically clean, add a bridge theorem to:

~~~text
DkMath.CosmicFormula.HalfUnitZeroConjugate.halfUnit u = u / 2
~~~

Do not move or redefine that existing real API.

## Part D — PowerGapBeam connection

Add a thin theorem explaining the d = 2 relation to the existing PowerGapBeam layer.

For example, with endpoints x and x+u:

~~~text
powerGap x (x+u) = u
powerBeam 2 x (x+u) = 2*x + u
~~~

and therefore:

~~~text
(x+u)^2 - x^2 = u * (2*x+u).
~~~

Reuse existing PowerGapBeam theorems. Do not create a second difference-factorization proof.

This connection is important because GAGE-005 will use exactly this d = 2 Gap/Beam split for FLT2.

## Part E — dyadic refinement vocabulary

Keep this checkpoint minimal.

If useful, introduce only one semantic alias/definition for the half-step or midpoint in a characteristic-zero field, for example:

~~~text
dyadicHalfStep u = u / 2
dyadicMidpoint x u = x + u/2
~~~

but do not build a full dyadic lattice hierarchy here. DkMath already has separate dyadic-analysis modules, and this checkpoint is about exponent correction, not mesh topology.

## Part F — generic higher-degree defect reconnaissance

Investigate whether a short generic theorem can be proved for the scaled defect.

The expected algebraic expansion is:

~~~text
scaledMidpointDefect d x u
  = sum over odd j >= 3 of
      choose(d,j) * (2*x+u)^(d-j) * u^j.
~~~

This formula explains why d = 2 has no higher correction terms.

However:

- do not force this theorem if parity-filtered binomial bookkeeping becomes large;
- do not re-prove the binomial theorem;
- do not block Outcome A on this generic expansion.

If the generic expansion is not proof-thin, record it as the first deferred target after the low-degree calibration.

## Part G — positivity / uniqueness reconnaissance

Investigate, but do not require for Outcome A, a theorem of the form:

~~~text
3 <= d, 0 < u, 0 <= x
  -> 0 < scaledMidpointDefect d x u
~~~

over ℝ or another ordered characteristic-zero carrier.

This would formalize the stronger claim:

~~~text
d = 2 is the unique nonlinear exponent with zero midpoint correction
~~~

in the positive domain.

Do not invoke heavy calculus unless clearly simpler than the algebraic route. If generic positivity is nontrivial, defer it explicitly.

Do not state uniqueness merely from the d = 2 and d = 3 calibrations.

## Important semantic distinction

The theorem:

~~~text
scaledMidpointDefect 2 = 0
~~~

supports the statement:

~~~text
the square power difference closes exactly at the midpoint main term.
~~~

It does NOT by itself prove FLT2, nor does it say x = u is required.

Also preserve:

~~~text
x = u
  -> all monomials x^(d-k) u^k collapse to the same base value x^d
~~~

as a separate self-similarity observation if you choose to add a tiny theorem. Do not conflate that all-d fact with the d = 2 midpoint-closure uniqueness.

## Tests

Create:

~~~text
DkMathTest/NumberTheory/Gauge/Dyadic.lean
DkMathTest/NumberTheory/Gauge/DyadicAxiomAudit.lean
~~~

Calibrate at least:

~~~text
d = 2, arbitrary symbolic x,u
d = 3, arbitrary symbolic x,u
d = 4, arbitrary symbolic x,u
x = 1, u = 1, d = 3 -> defect = 1
x = 1, u = 1, d = 4 -> defect = 12
~~~

Also test the half-unit identity on a concrete rational or real example if such a theorem is added.

## No-go expansion

Do not implement:

- FLT2 factor splitting;
- primitive parity/gcd analysis;
- CyclotomicGaugeBridge;
- AdditiveLanding;
- generic FLT;
- a new dyadic mesh framework;
- a derivative-based theory of finite differences.

## Axiom / safety constraints

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

Run #print axioms on every substantive theorem.

## Validation

Run at least:

~~~text
lake build DkMath.NumberTheory.Gauge.Dyadic
lake build DkMath.NumberTheory.Gauge
lake build DkMathTest.NumberTheory.Gauge.Dyadic
lake build DkMathTest.NumberTheory.Gauge.DyadicAxiomAudit
lake build DkMath
git diff --check
~~~

Record the full build job count.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-004.md
~~~

The report must include:

- Outcome A/B;
- exact public API added;
- scaled defect definition and why division-free form was chosen;
- d = 2,3,4 calibration proofs;
- half-unit identity and carrier assumptions, if added;
- PowerGapBeam reuse map;
- result of generic odd-correction expansion reconnaissance;
- result of generic positivity/uniqueness reconnaissance;
- any self-similarity theorem added, if any;
- files changed;
- focused/full build results;
- axiom audit;
- forbidden-token scan;
- git diff summary;
- whether GAGE-005 may proceed unchanged.

Preferred Outcome A:

The denominator-free midpoint defect is a stable public Gauge API, d = 2 vanishes exactly, d = 3 and d = 4 expose nonzero higher corrections, and the square midpoint identity is connected to the existing PowerGapBeam factorization.

Stop after GAGE-004. Do not implement GAGE-005.