# Instruction 030 - Singleton-prime cofactor-window bound

## Mission

Continue from Instruction 029.

Instruction 029 proved exact same-prime-base fibers:

  F(n,p,y) = Icc(L+1,min(U,v))

with exact cardinality and von Mangoldt weight.

It also proved that bases p > 2*n have only depth one. Therefore repeated-power compression cannot improve the dominant singleton-prime sector.

The next question is whether that singleton sector has an independent finite geometric bound.

Do not assume such a bound exists.

## Main research question

For n >= 3, consider the weighted singleton-prime occupancy suggested by Report 029:

  Q(n) =
    sum over k in Icc(2,n-1)
      sum over primes p satisfying
        p > 2*n
        n^2 / k < p
        p <= (n^2 + 2*n) / k
      of log(p).

A contributing pair (k,p) corresponds to the shell target p*k.

Determine whether this cofactor-window representation yields any genuinely new upper bound on the singleton-prime mass, independent of the existing carry inventory.

The key distinction is:

  exact reindexing is not yet a gain;
  an independent upper estimate that improves the 028/029 budget is a gain.

## First audit: what is Q really measuring?

Before adding a new hierarchy of definitions, determine precisely how Q relates to:

- old large prime carry labels,
- occupied singleton targets,
- next-shell-multiple uniqueness,
- the divisor / von-Mangoldt identities from 028,
- any existing quotient or cofactor-window APIs.

If Q is exactly an existing mass under another coordinate system, prove the thin bridge and say so.

Check whether the condition p > 2*n forces useful uniqueness or disjointness among the cofactor windows. Formalize such a fact only if it materially helps the estimate.

Do not confuse disjoint indexing with a numerical saving.

## Bound search

Audit existing elementary finite bounds before introducing new analytic machinery.

Possible forms may involve:

- quotient-window cardinality,
- interval length,
- factorial or binomial product bounds,
- Chebyshev/von-Mangoldt finite sums already available in Mathlib or DkMath,
- a direct weighted cofactor inequality.

Let the repository decide the natural formulation.

A candidate U(n) is useful only if it is independent of the carry-event inventory and can be inserted into the existing budget as a true upper estimate for the singleton-prime mass.

Do not import PNT, RH, or an unproved short-interval prime estimate merely to force progress.

If a useful bound would require genuinely new analytic prime-distribution input, identify that frontier explicitly instead of hiding it inside a weak envelope.

## Acceptance test

Decompose the 029 large mass into:

  repeated-power contribution
  + singleton-prime contribution.

Use the exact 028/029 ledger.

If Q(n) or an equivalent singleton mass has an independent bound U(n), test the resulting consumer of the form

  small carry
  + repeated-power contribution
  + U(n)
  + higher correction
  < log(cell).

The exact names and decomposition may differ; reuse existing production APIs.

The decisive question is whether the new estimate is strictly stronger than the existing exact ledger for all relevant n, or at least establishes a new unconditional range not already covered.

A bound that is always above the exact singleton mass but gives no new strict margin is not Outcome A.

## Failure modes to preserve

Valid conclusions include:

- Q is only a quotient-window reindexing of an existing divisor mass;
- the best elementary bound is too loose to improve the budget;
- a useful estimate reduces to short-interval prime-weight control not present in the current library;
- a nontrivial finite bound exists but is not yet globally strong enough.

Preserve smallest or clearest counterexamples to proposed stronger inequalities.

## Implementation policy

Work autonomously.

Choose theorem names, modules, helper lemmas, diagnostics and proof strategy.

Keep the production surface small.

Prefer:

  exact identification
  -> one useful independent bound, if it exists
  -> one consumer
  -> audit

Do not build a large speculative hierarchy.

Do not predesign Instruction 031.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics when useful.

Diagnostics are evidence for choosing a theorem, not proof premises.

## Outcome classification

Outcome A:

A new independent singleton-prime bound is formalized and yields a strict improvement or a new unconditional prime-existence range in the 028/029 consumer.

Outcome B:

A genuine new exact bridge or independent bound is formalized, but no universal strict budget improvement follows.

Outcome C:

The cofactor-window route is only a reindexing, or all available elementary bounds are too weak to add arithmetic information.

All three outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-030.md

State:

- the exact meaning of Q or its chosen equivalent,
- whether cofactor windows give any useful uniqueness/disjointness,
- the strongest independent bound proved,
- whether the bound is genuinely new or only a reindexing,
- its effect on the 028/029 budget,
- diagnostics/counterexamples,
- axiom and build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
