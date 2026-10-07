# Instruction 032 - Least-prime-factor rough-composite error

## Mission

Continue from Instruction 031.

Instruction 031 proved an independent finite-wheel bound

  Q <= W <= G

and the exact remaining error identity

  V = Q + E,

where E is the accumulated logarithmic weight of surviving nonprime cofactor-window integers.

The 30-wheel removes the n=7 obstruction, but E is nonzero from n=9 onward and is large enough to break the strict consumer at n=29.

The next question is whether the surviving composite error E has an independent factor-pair bound that is strong enough to reduce the accumulated budget.

Do not assume that a larger fixed wheel is the answer.

## Main research question

For a surviving composite q in a cofactor window, group q by its least prime factor.

Because q survives the chosen finite prime basis, its least prime factor lies beyond that basis. Write conceptually

  q = r * m

with r = minFac(q).

Determine whether the resulting least-prime-factor fibers and factor-pair geometry give a useful independent upper bound for E.

The desired estimate must not depend on the actual prime carrier Q or on carry-event membership.

## First task: exact rough-composite normal form

Starting from the 031 sieve carrier, prove the strongest clean structural facts available for a surviving composite q.

Audit and reuse existing minFac, rough-factorization, quotient, reduced-residue and factor-pair APIs before adding new definitions.

Questions include:

- how large must minFac(q) be relative to the chosen wheel basis?
- what exact restrictions follow for the complementary factor m=q/minFac(q)?
- can q=r*m be placed in an endpoint interval depending only on n, k and r?
- are least-prime-factor fibers disjoint or canonically indexed?

If these are only exact reindexings, say so.

## Required calibration points

Preserve the existing small obstructions and examples.

In particular explain structurally:

- n=9, q=49=7^2,
- n=12, q=77=7*11,
- the surviving composites at n=29.

The implementation should show how these arise in the least-prime-factor description rather than merely recomputing them.

## Bound search

Seek one independent finite upper bound for the accumulated composite error E.

Possible useful forms include:

- a cardinal bound for each least-factor fiber,
- an endpoint interval bound for the complementary factor,
- a product or logarithmic bound for all factor pairs in one window,
- a square-root / roughness bound using r <= sqrt(q),
- another elementary factor-pair estimate already supported by DkMath or Mathlib.

Let the mathematics choose the form.

The important criterion is the total accumulated error across all cofactor windows, including window multiplicity.

Do not replace E by an exact factorization sum and call that a new bound.

## Budget test

If an independent error bound F(n) is obtained, use

  E <= F

to refine the 031 singleton envelope and reconnect it to

  oldBudget
  = higher
  + small carry
  + repeated large carry
  + singleton mass.

Compare the new consumer against the exact ledger and the 031 wheel consumer.

Outcome A requires a genuine strict improvement: a universal budget gain or a new unconditional prime-existence range not already available from the exact ledger.

A useful factor-pair theorem without such a gain is Outcome B.

## Adaptive-wheel caution

A complete factor-test basis can remove every composite and recover Q exactly.
That is classification, not an independent quantitative estimate.

If the least-factor analysis merely says that the wheel should be enlarged until every possible minFac is included, classify that as a limitation rather than progress.

Likewise, do not import PNT, RH, or an unproved short-interval sieve theorem merely to force closure.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof strategy.

Keep the production surface small.

Prefer:

  exact least-factor normal form
  -> one independent factor-pair bound
  -> one budget consumer
  -> obstruction/frontier audit

Do not build a large speculative hierarchy.

Do not predesign Instruction 033.

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

A least-prime-factor / factor-pair bound is formalized and yields a strict budget improvement or new unconditional prime-existence range.

Outcome B:

A genuine new rough-composite normal form or independent error bound is formalized, but no universal strict budget improvement follows.

Outcome C:

The least-factor route is only an exact reindexing, reduces to adaptive complete sieving, or the missing estimate is genuinely a short-interval weighted sieve problem.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-032.md

State:

- the exact least-prime-factor normal form,
- how n=9, n=12 and n=29 appear in it,
- the strongest independent factor-pair/error bound proved,
- whether it is more than a reindexing,
- effect on the 031 error and the 028-031 budget,
- diagnostics and counterexamples,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
