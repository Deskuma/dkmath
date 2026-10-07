# Instruction 038 - Aggregate central-carry compensation

## Mission

Continue from Instruction 037.

Instruction 037 proved a genuine phase-aware correction bound, but the stronger
candidate

  gnomonPascalSmallCarryMass n
    <= log (Nat.choose (2*n) n)

remains unresolved.

A pointwise carry inclusion is false. At n=4,d=3 the square-shell small carry
is one while the central-binomial carry is zero.

The next question is whether the inequality nevertheless holds after exact
weighted cancellation of the coordinates shared by the two carry systems.

Do not replace this aggregate problem by another local exclusion heuristic.

## Main research question

Express the central-binomial logarithm in the same prime-power coordinate
currency as the small carry.

For a prime power d=p^a, the central coefficient should contribute one
von Mangoldt weight exactly when the corresponding central carry coordinate is
active, with multiplicity across exponents recovering the p-adic valuation.

Audit the existing Mathlib/DkMath factorization_choose and Kummer receivers and
prove only the thin bridge needed for this comparison.

Then split the two finite prime-power carriers into:

  common coordinates,
  small-only coordinates,
  central-only coordinates.

After cancelling the common mass, determine whether

  sum_{small-only d} vonMangoldt(d)
    <=
  sum_{central-only d} vonMangoldt(d)

holds for every n.

This is the exact compensation statement behind the unresolved central-binomial
candidate.

## Equivalent formulations

If useful, repackage the weighted comparison as a positive integer product:

  product of prime bases contributed by small-only prime-power coordinates
    <=
  product of prime bases contributed by central-only coordinates.

The precise encoding is up to the implementation.

Do not require divisibility unless it is actually true. The n=4 regression
already warns that the small-only product need not divide the central
binomial coefficient.

A product inequality, weighted injection, monotone matching, or another exact
finite comparison is acceptable.

## Required regressions

Preserve:

- n=4,d=3 as a pointwise-inclusion counterexample,
- n=27, where Instruction 037 kernel-checked the full central-binomial
  inequality and diagnostics found the tightest sampled ratio,
- representative anchors 32,69,210,297,1031,5000.

At n=4 the implementation should show where the missing log(3) is compensated
in the central-only side, without claiming coordinatewise domination.

## Search policy

Work autonomously.

Possible structures to inspect include:

- residue pairing between d <= 2*n coordinates,
- prime-power exponent chains of a fixed base,
- floor/carry identities for choose(2*n,n),
- product inequalities after grouping by prime base,
- complementary residue classes,
- finite involutions or monotone matchings.

Do not assume that compensation occurs within the same prime base.
The n=4 example already suggests cross-base compensation may be necessary.

Do not build a general arbitrary-binomial carry framework.

## If the universal compensation is proved

Derive the original target

  smallCarry(n) <= log(choose(2*n,n)).

Then replace the Instruction 037 phase-exclusion small bound by the central
binomial bound in the non-singleton correction envelope.

Retain the repeated-large band budget and the existing reciprocal higher
correction.

Expose one stronger correction budget B_central with

  C_ns(n) <= B_central(n).

Compare it with B_phase and B_036 where possible.

Provide the conditional consumer

  Q + B_central(n) < log(cell)
    -> exists prime in SquareCell n.

This remains a sufficient criterion unless a separate equivalence is proved.

## If the universal compensation is false

Produce a smallest or structurally clear counterexample to the aggregate
weighted comparison.

Preserve the exact small-only and central-only weighted defect.

Then ask whether a corrected inequality with one explicit endpoint or residue
error term is true and materially sharper than Instruction 037.

Do not hide the defect inside a tautological correction.

## Quantitative interpretation

The important issue is not merely whether the central candidate is true.

Measure how much correction slack remains after the strongest proved aggregate
comparison.

Instruction 037 already made the n=5000 reduced diagnostic positive.
The harder retained failures were still around anchors such as 69 and 297.

Determine whether aggregate central compensation removes those remaining
correction-envelope failures or whether Q / another term still dominates.

Diagnostics are not proof premises.

## Circularity guard

The following do not count as progress:

- defining the compensating right-hand side from the exact small-carry mass,
- querying Q or the target shell prime inventory,
- assuming the old strict criterion,
- proving only a finite numerical range and extrapolating it,
- replacing the desired inequality by an equivalent statement with no new
  proof mechanism.

The compensation theorem itself, if proved, is the new mathematics.

## Stopping rule

This checkpoint should settle the aggregate central-binomial route as far as
possible.

Either:

- prove the compensation inequality,
- refute it,
- or identify a precise structural obstruction that prevents the existing
  carry APIs from comparing the two weighted difference sets.

Do not respond by widening the fixed quadratic exclusion radius from
Instruction 037.

Do not predesign Instruction 039.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

The aggregate compensation theorem and resulting correction budget yield a
universal strict budget theorem or a genuinely new unconditional
prime-existence range.

Outcome B:

The aggregate central-binomial comparison is proved, or a substantial corrected
weighted comparison is formalized, and the independent correction budget is
strictly improved, but universal closure is not obtained.

Outcome C:

The aggregate central-binomial comparison is false, or no non-tautological
weighted compensation theorem can be obtained from the available structure.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-038.md

State:

- the exact central prime-power carry carrier used,
- the common / small-only / central-only decomposition,
- the status of the aggregate compensation inequality,
- how n=4,d=3 is compensated or defeats the proposal,
- the strongest resulting small-carry bound,
- the resulting correction budget and comparison with 037/036,
- diagnostics at retained anchors,
- whether remaining correction slack is still decisive,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
