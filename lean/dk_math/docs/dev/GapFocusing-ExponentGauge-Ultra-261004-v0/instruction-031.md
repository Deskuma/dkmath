# Instruction 031 - Cofactor-window finite sieve error

## Mission

Continue from Instruction 030.

Instruction 030 proved:

- Q is exactly the singleton-prime large carry mass.
- Cofactor windows have unique prime carriers.
- Independent endpoint-only binomial and odd-spacing bounds exist.
- The combined geometric envelope G is still too loose for a universal budget gain.
- The first certified failure of the strict consumer is n=7.

The next question is whether the excess G-Q can be reduced by a finite sieve that removes composite-only mass inside the cofactor windows.

Do not assume that a fixed wheel is sufficient.

## Main research question

Can the singleton-prime cofactor-window mass be bounded by a finite sieve estimate whose accumulated error is:

- independent of carry-event membership,
- strictly smaller than the current geometric envelope,
- and strong enough to improve the exact 028-030 budget?

Use existing wheel, reduced-residue, Möbius, parity, quotient and cofactor APIs wherever possible.

The main object is still the exact singleton mass Q from Instruction 030.

## First task: identify the right sieve carrier

For each cofactor window, compare its raw endpoint interval with natural filtered carriers such as:

- odd integers,
- residues avoiding a finite small-prime basis,
- reduced residues modulo a suitable finite wheel,
- any existing DkMath carrier that already models the same exclusion.

Do not build a new general sieve framework if an existing one can be adapted.

Prove thin bridge theorems first.

A filtered carrier is useful only if its remaining weighted envelope can be estimated without referring to the actual prime inventory or carry events.

## Required sanity check

Preserve the n=7 obstruction from Instruction 030.

At n=7, the window (14,15] carries no prime but the current endpoint envelope charges mass.

Any proposed sieve bound should explain whether and how that composite-only contribution is removed.

Also test whether the same mechanism introduces compensating overcount elsewhere.

Do not optimize only for this example.

## Bound search

Look for one useful finite weighted estimate.

Possible tools include:

- existing primorial-wheel and projected-wheel APIs,
- reduced-residue cardinalities,
- exact odd/Möbius corrections,
- finite product divisibility,
- endpoint products after deleting small-prime multiples,
- another elementary finite sieve already present in DkMath or Mathlib.

The desired theorem may be a cardinal bound, product bound, logarithmic bound, or exact correction identity.

Let the mathematics decide.

The important quantity is the accumulated error over all cofactor windows, not only the quality of one local interval.

## Budget test

If a filtered singleton envelope W(n) is obtained, connect it to the exact split

  oldBudget
  = higher
  + small carry
  + repeated large carry
  + singleton mass.

Test whether replacing the singleton mass by W gives a genuinely stronger consumer than Instruction 030.

Outcome A requires an actual strict improvement: either a universal strict budget gain or a new unconditional range not already provided by the exact ledger.

An upper bound with nonnegative excess but no new margin is Outcome B.

## Analytic frontier

If every useful finite sieve estimate ultimately requires nontrivial short-interval prime-weight control, say so explicitly.

Do not import PNT, RH, or an unproved short-interval theorem merely to force Outcome A.

A precise statement of the missing short-interval estimate, in the coordinates exposed by the cofactor windows, is a valid result.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof strategy.

Keep the production surface small.

Prefer:

  thin carrier bridge
  -> one filtered weighted estimate
  -> one budget consumer
  -> obstruction/frontier audit

Do not build a large speculative sieve hierarchy.

Do not predesign Instruction 032.

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

A finite sieve bound is formalized and yields a strict budget improvement or new unconditional prime-existence range.

Outcome B:

A genuine filtered carrier theorem or independent weighted sieve bound is formalized, but no universal strict budget improvement follows.

Outcome C:

The available finite sieve structure reduces only to reindexing / weak endpoint bounds, or the remaining useful estimate is genuinely a short-interval prime-distribution problem.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-031.md

State:

- the filtered carrier actually used,
- its exact relation to the 030 cofactor windows,
- the strongest weighted bound or correction proved,
- what happens to the n=7 obstruction,
- the accumulated sieve error,
- effect on the 028-030 budget,
- diagnostics and counterexamples,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
