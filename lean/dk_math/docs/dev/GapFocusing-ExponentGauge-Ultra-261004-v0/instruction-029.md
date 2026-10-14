# Instruction 029 - Same-prime-base fiber bound

## Mission

Continue from Instruction 028.

Instruction 028 established exact identities for n >= 3:

  log(cell) = shellVM + lowCarryMass

  oldBudget = higherCorrection + lowCarryMass

These identities are now kernel facts. However, they did not by themselves produce a new universal upper bound, so Instruction 028 was Outcome B.

The next research question is narrower.

When multiple prime-power labels contribute to the same shell image / target, diagnostics suggest that the remaining collisions are organized along powers of the same prime base.

Study that structure directly.

Do not assume in advance that the right invariant is fiber cardinality. If exponent width, valuation mass, reciprocal-exponent mass, or another same-base quantity is the natural exact bound, use that instead.

The goal is to determine whether same-prime-base fibers supply a genuinely stronger constraint that can be consumed by the Instruction 028 budget identities.

## Main research question

For a fixed prime p and a fixed shell target y, consider the exponents a for which a prime-power label p^a contributes to y.

Conceptually:

  F(p,y) = { a | p^a maps to y }

Determine what exact restrictions follow from the existing shell geometry, prime-power routing, valuation, and monotonicity APIs.

In particular, investigate whether one can prove a nontrivial finite bound of the form:

  card F(p,y) <= C(n,p)

or a stronger weighted statement that is more natural for the 028 decomposition.

Do not force this exact shape if the repository structure suggests a better theorem.

## Required starting point

Read first:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-028.md

Reuse the production definitions and theorems from Instruction 028.

Also audit the immediately relevant prime-power, valuation, von-Mangoldt/log-mass, shell-routing, and large-label modules already used by 025-028.

Prefer existing APIs over new abstractions.

## Questions to answer

1. Collision classification

Determine precisely when two distinct prime-power labels can map to the same target.

If the statement

  same target -> same prime base

is true under explicit hypotheses, formalize it.

If it is false, preserve the smallest counterexample and state the correct classification.

2. Same-base exponent geometry

For p^a and p^b in the same fiber, identify the exact arithmetic restriction on a and b.

Look for consequences of:

  p^a < p^b
  shell-width bounds
  target interval bounds
  monotonicity of powers
  valuation identities

The useful invariant may be:

  b - a
  number of admissible exponents
  total valuation weight
  log-weight
  another exact quantity

Let the mathematics decide.

3. Fiber upper bound

If a nontrivial same-base bound exists, expose it as a reusable production theorem.

The bound should be strong enough to say more than mere finiteness.

Avoid introducing analytic prime-distribution results only to obtain a bound.

4. Consume the bound in Instruction 028

Test whether the new fiber theorem gives a strict improvement when inserted into:

  oldBudget = higherCorrection + lowCarryMass

or the equivalent shell log-mass decomposition.

This is the main success criterion.

A beautiful fiber theorem that does not improve the global budget is still useful, but it is Outcome B rather than Outcome A.

5. Failure mode

If no useful bound survives, explain exactly why.

Examples of acceptable conclusions include:

- fibers can be arbitrarily long within the available hypotheses
- the best bound is already implicit in an existing theorem
- the bound is exact but too weak to improve oldBudget
- cardinality is the wrong observable but a weighted invariant survives

Do not manufacture a stronger claim.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, proof strategy, and diagnostics as appropriate.

Keep the production surface small.

Do not reproduce a long speculative architecture in the codebase.

Prefer:

  research question
  minimal exact theorem
  consumer
  audit

over a large hierarchy of provisional definitions.

If a proposed route fails, record the obstruction in report-029.md instead of encoding dead machinery.

## Validation

Run the same standard expected for this branch:

- focused build for changed modules
- relevant facade build
- root build if appropriate
- axiom audit for new production declarations
- bounded diagnostics where useful

Diagnostics may extend the Instruction 028 range when cheap, but a larger brute-force range is not itself a result.

## Outcome classification

Outcome A:

A genuinely new same-prime-base fiber constraint is formalized and it yields a strict improvement to the Instruction 028 budget / obstruction.

Outcome B:

A genuine new fiber theorem or exact weighted constraint is formalized, but no universal strict budget improvement follows yet.

Outcome C:

The proposed fiber direction collapses to existing bounds, is false, or supplies no new arithmetic restriction beyond current APIs.

All three outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-029.md

The report should state:

- exact production theorems added
- what the fiber actually is
- whether collisions are same-base only
- the strongest proven bound or weighted invariant
- whether it improves the 028 oldBudget decomposition
- diagnostics and smallest counterexamples where relevant
- axiom/build status
- Outcome A/B/C
- the next natural frontier

Do not predesign Instruction 030 unless the result of 029 clearly identifies it.
