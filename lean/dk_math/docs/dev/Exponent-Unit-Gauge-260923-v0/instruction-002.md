# GAGE-002 — Prime-power purity detector

Branch:

~~~text
research/Exponent-Unit-Gauge-260923-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/README.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/ROADMAP.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-001.md
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/review-001.md
~~~

## Objective

Close the reverse direction of the Pascal exponent gauge:

~~~text
a prime p supports every interior coefficient of row n
    + nontrivial row 1 < n
    -> n is a positive power of that same prime p
~~~

Then expose a row-level interior-gcd detector for prime-power purity.

This checkpoint should reuse Mathlib Lucas/binomial theorems rather than re-prove Lucas's theorem or Kummer carry theory.

## Step 0 — verify pinned Mathlib API

Inspect the project's pinned Mathlib version before changing production code.

Search especially:

~~~text
Mathlib.Data.Nat.Choose.Lucas
Mathlib.Data.Nat.Choose.Factorization
Mathlib.Data.Nat.Multiplicity
~~~

Current upstream Mathlib exposes declarations equivalent to:

~~~text
eq_pow_multiplicity_of_choose_modEq_zero_nat
gcd_choose_eq_minFac_of_isPrimePow
gcd_choose_eq_one_of_not_isPrimePow
~~~

Do not assume exact namespaces or signatures from this instruction. Record the exact pinned declarations used.

## Production ownership

Primary owner remains:

~~~text
DkMath/NumberTheory/Gauge/Exponent.lean
~~~

Only create another exponent-specific production file if the implementation becomes materially clearer. Do not create Value/Dyadic/Landing files here.

## Part A — same-prime reverse characterization

Target a theorem of the following semantic shape:

~~~lean
theorem innerRowSupportPrime_eq_prime_pow
    {n p : ℕ}
    (hn : 1 < n)
    (h : DkMath.NumberTheory.InnerRowSupportPrime n p) :
    ∃ e : ℕ, 0 < e ∧ n = p ^ e := ...
~~~

Equivalent naming is acceptable if repository style suggests a better name.

Required proof discipline:

1. Extract p.Prime and AllInnerChooseDivisible n p from h.
2. Convert interior divisibility to the MOD-p hypothesis expected by Mathlib's Lucas converse theorem.
3. Obtain an exact equality n = p ^ e, ideally with the canonical multiplicity exponent supplied by Mathlib.
4. Prove e > 0 from hn : 1 < n. Do not add positivity as an axiom or choose an unrelated exponent witness.

Prefer also exposing the canonical equality form if useful:

~~~text
n = p ^ multiplicity p n
~~~

but do not duplicate it if it would leak awkward implementation-specific types into the public facade.

## Part B — iff form

If Part A is clean, expose the practical characterization:

~~~text
InnerRowSupportPrime n p
  iff
p is prime and n = p^e for some e > 0
~~~

under the explicit boundary hypothesis:

~~~text
1 < n
~~~

The reverse direction must reuse the existing prime-power row support theorem.

Do not claim an unconditional iff for n = 0 or n = 1.

## Part C — Pascal interior gcd detector

Add a thin row-level gauge quantity if no equivalent project definition already exists.

Preferred shape:

~~~lean
def/abbrev exponentGaugeInteriorGCD (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).gcd n.choose
~~~

Search first for an existing DkMath definition. Do not duplicate one if found.

Then expose wrappers over Mathlib's gcd theorems:

### C1. Prime-power row

For Nat.IsPrimePow n:

~~~text
exponentGaugeInteriorGCD n = n.minFac
~~~

### C2. Non-prime-power row

For 1 < n and not Nat.IsPrimePow n:

~~~text
exponentGaugeInteriorGCD n = 1
~~~

### C3. Detector

If it stays proof-thin, prove one useful iff, for example:

~~~text
1 < n ->
(exponentGaugeInteriorGCD n != 1 <-> Nat.IsPrimePow n)
~~~

or:

~~~text
1 < n ->
(1 < exponentGaugeInteriorGCD n <-> Nat.IsPrimePow n)
~~~

Choose the form requiring the least extra arithmetic.

Do not overbuild both unless they are essentially one-line consequences.

## Part D — connect to Gauge facade

Keep the existing meanings:

~~~text
PrimeExponentGauge p
PrimePowerExponentGauge p e
exponentGaugeHeight p n k
~~~

Do not redefine them.

If a new theorem gives a natural facade statement such as:

~~~text
nontrivial common support prime -> pure prime-power exponent gauge
~~~

add it only as a semantic theorem.

## Important edge cases

Explicitly test:

~~~text
n = 1
n = p
n = p^2
n = 6
n = 12
~~~

The production reverse theorem must not accidentally accept n = 1 because the interior condition is vacuous there.

Examples for 6 and 12 should demonstrate detector failure or gcd = 1, not require theorem-level special cases.

## Imports

Import the smallest required Mathlib owner directly if PascalPrimeDial does not already provide it transitively.

Likely candidate:

~~~text
Mathlib.Data.Nat.Choose.Lucas
~~~

Do not import Mathlib wholesale.

## Tests

Extend/create focused tests under:

~~~text
DkMathTest/NumberTheory/Gauge/Exponent.lean
DkMathTest/NumberTheory/Gauge/ExponentAxiomAudit.lean
~~~

Test at least:

- row 3 is detected as 3^1;
- row 9 is detected as a 3-power;
- row 8 is detected as a 2-power;
- row 6 has interior gcd 1;
- row 12 has interior gcd 1;
- the reverse theorem requires/provides the nontrivial-row hypothesis explicitly.

Use theorem-driven examples where practical; small norm_num/native_decide checks are acceptable only as calibration, not as the general proof.

## Axiom / safety constraints

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

Run #print axioms on every new substantive theorem.

## Forbidden expansion

Do not implement:

- ValueGauge;
- midpoint/dyadic correction;
- FLT2;
- cyclotomic bridges;
- AdditiveLanding;
- any general FLT statement.

Do not formalize Lucas's theorem from scratch if the pinned Mathlib theorem closes the target.

## Validation

Run focused builds for all changed gauge/test modules, then:

~~~text
lake build DkMath.NumberTheory.Gauge
lake build DkMath
git diff --check
~~~

Record exact job count for the full build.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/Exponent-Unit-Gauge-260923-v0/report-002.md
~~~

The report must include:

- Outcome A/B;
- exact pinned Mathlib declarations used;
- proof path for the reverse characterization;
- treatment of n = 0,1 vacuity;
- public API added;
- gcd detector API added, if any;
- examples/calibrations;
- files changed;
- focused/full build results;
- axiom audit;
- forbidden-token scan;
- git diff summary;
- whether GAGE-003 may proceed unchanged.

Preferred Outcome A:

The exponent gauge now detects exactly the nontrivial prime-power rows, using the same prime support p, and exposes the interior Pascal gcd as a prime-power purity detector.

Stop after GAGE-002. Do not implement GAGE-003.
