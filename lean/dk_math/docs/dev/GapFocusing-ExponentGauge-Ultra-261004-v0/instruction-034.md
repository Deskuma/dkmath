# Instruction 034 - Ordered three-prime composite witness

## Mission

Continue from Instruction 033.

Instruction 033 proved a collision-safe semiprime lower witness D <= E.
Its product map is injective, it subsumes the square correction, and it repairs
the failed 032 consumer at n=31.

The remaining error is higher-composite weight. At n=32 the explicit residual is

  343 = 7^3
  539 = 7^2 * 11.

These are both products of exactly three prime factors counted with multiplicity.

The next question is whether the three-prime layer supplies a substantial
independent lower composite witness, or whether continuing factor-depth
classification is becoming exact factorization rather than a useful bound.

Do not assume that a full factor-count hierarchy should be built.

## Main research question

Investigate ordered prime triples

  r <= s <= t

whose product lies in a cofactor window and whose factors survive the chosen
finite wheel.

Can their distinct products be certified as a collision-safe lower subset of
the remaining composite carrier, and does subtracting their log weight
materially reduce the residual error left by Instruction 033?

The witness must be defined from endpoint/factor conditions, not by filtering
the actual composite inventory.

## Collision-safe triple carrier

Audit existing roughTriple / product-wave / factorization APIs before adding
new machinery.

A natural candidate is an endpoint-defined carrier satisfying

  r,s,t prime,
  r <= s <= t,
  each factor coprime to the wheel product,
  A < r*s*t <= B.

Do not force this exact representation if an existing API gives a cleaner
ordered multiset carrier.

Prove that the product map is injective, or otherwise give an exact collision
correction, before using the triple weight as removable composite mass.

Repeated factors must be handled correctly.

In particular the carrier should be able to explain

  343 = 7*7*7
  539 = 7*7*11

without ambiguity.

## Interaction with the semiprime witness

Do not double-charge products already removed by Instruction 033.

Prove the required disjointness between the semiprime product image and the
three-prime product image, or define a combined distinct-product carrier whose
semantics make this automatic.

The combined removable mass must still satisfy a theorem of the form

  D3 <= E

where D3 includes the previously certified semiprime mass and the newly
certified three-prime mass exactly once.

## Required calibration points

Preserve at least:

- n=9 and 49,
- n=12 and 77,
- n=31, where the semiprime witness already closes the independent consumer,
- n=32, where the residual {343,539} should test the three-prime layer,
- the first failing region seen in Instruction 033 diagnostics, including n=210,
- retained larger anchors such as 297, 1031 and 5000.

Determine how much residual mass is actually removed at these anchors.

## Quantitative stopping test

This checkpoint must decide whether factor-depth continuation is worthwhile.

After adding the three-prime witness, measure the remaining independent excess

  E - D3.

Compare it with the exact-ledger margin and with the 033 residual.

If the three-prime layer gives a substantial new reduction and changes the
frontier materially, record that.

If the remaining mass is still large and would naturally require four-prime,
five-prime, ... witnesses, do not automatically prescribe that hierarchy.
State whether this route is converging toward complete factor classification
rather than an independent quantitative estimate.

## Budget test

Reconnect the corrected singleton envelope to the exact ledger

  oldBudget
  = higher
  + small carry
  + repeated large carry
  + Q.

Compare the new consumer with Instruction 033.

Outcome A requires the existing project-level criterion: a universal strict
budget result or a genuinely new unconditional prime-existence range beyond
the exact ledger.

Recovering finite failures remains Outcome B when the exact ledger already
covers them.

## Frontier caution

A complete ordered-prime-factor expansion of every surviving composite would
eventually reproduce the exact composite carrier E and hence Q.

That is exact classification, not a new distribution estimate.

Instruction 034 should therefore be treated as a diagnostic checkpoint on the
factor-depth strategy, not as the start of an unbounded hierarchy.

If three-prime deletion still leaves a large higher-factor residual, identify
the remaining weighted short-window problem explicitly.

Do not import PNT, RH, or an unproved analytic estimate merely to force closure.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof
strategy.

Keep the production surface small.

Prefer:

  collision-safe three-prime carrier
  -> combined certified lower mass
  -> one corrected envelope / consumer
  -> factor-depth stopping decision

Do not predesign Instruction 035.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

Diagnostics may guide theorem selection but are not proof premises.

## Outcome classification

Outcome A:

The three-prime correction yields a universal strict budget improvement or a
genuinely new unconditional prime-existence range.

Outcome B:

A genuine collision-safe three-prime lower witness and stronger envelope are
formalized, but global closure is not obtained.

Outcome C:

The three-prime layer adds little quantitative information, collapses toward
exact factor classification, or shows that further factor-depth enumeration
is not a useful independent route.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-034.md

State:

- the ordered three-prime carrier actually used,
- how product uniqueness and repeated factors are handled,
- how semiprime/triple disjointness is proved,
- how 343 and 539 are handled,
- the combined certified lower mass,
- the remaining residual E-D3,
- effect on n=210 and the retained larger anchors,
- effect on the exact 028-033 budget,
- whether factor-depth continuation remains mathematically worthwhile,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
