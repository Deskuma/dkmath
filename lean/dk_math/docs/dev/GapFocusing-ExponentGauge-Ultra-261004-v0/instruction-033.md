# Instruction 033 - Distinct semiprime composite witness

## Mission

Continue from Instruction 032.

Instruction 032 proved:

- an exact least-prime-factor normal form for surviving composites,
- an independent upper error bound E <= F,
- the orientation warning that an upper bound on E cannot be subtracted from V,
- a valid square witness L <= E,
- and the corrected singleton envelope

  Q <= U <= W.

The square witness repairs n=29 but the corrected consumer fails at n=31.

The next question is whether the nonsquare part of the surviving-composite error contains a large, collision-free semiprime subcarrier that can be certified from endpoints alone.

Do not assume that semiprimes are sufficient for global closure.

## Main research question

The 032 diagonal witness uses products r*r.

Now investigate off-diagonal products

  r*s,  r < s,

especially when r and s are prime factors surviving the fixed wheel.

Because distinct prime-factor pairs have unique products up to order, this may avoid the product collisions that invalidate the raw factor-pair sum.

Determine whether square and off-diagonal semiprime products together give a useful independent lower bound

  D <= E

large enough to improve the 032 corrected envelope.

The witness must remain independent of the actual singleton-prime carrier Q and of carry-event membership.

## First task: collision-free product carrier

Audit existing product-pair, rough-pair, collision and finite-wave APIs before defining a new carrier.

Seek a finite endpoint-defined carrier of certainly-composite products in each cofactor window with a proved injective or otherwise collision-controlled product map.

A natural candidate is the unordered prime-factor pair carrier

  r <= s,
  r and s prime,
  both surviving the wheel,
  A < r*s <= B,

but do not force this exact definition if a cleaner existing API or a stronger elementary carrier is available.

The square case r=s should recover or subsume the 032 diagonal witness.

The off-diagonal case should explain structurally why products such as 77=7*11 are safely removable.

## Collision regression

Preserve the 032 counterexample

  539 = 7*77 = 11*49.

A raw composite factor-pair cover may count this product more than once.

Any lower witness intended for subtraction must prove that its weighted products are distinct, or account exactly for collisions.

Do not subtract a pair-weight sum merely because every pair product is composite.

## Required calibration points

Retain at least the structural checkpoints:

- n=9 and 49=7^2,
- n=12 and 77=7*11,
- n=29, where the square witness already repairs the consumer,
- n=31, where the 032 corrected consumer fails,
- n=32 and the 539 duplicate-factorization regression.

Determine how much of the surviving-composite error is certified by the new distinct-product witness at these anchors.

## Quantitative question

Let D denote the certified distinct composite log weight, in whatever exact form the implementation selects.

Prove

  D <= E

without using the actual composite filter as the definition of D.

Then form the corresponding corrected singleton envelope by deleting only D from the 031 sieve mass, capped by existing envelopes as needed.

Measure the exact remaining excess over Q.

The important question is not whether D is nonzero, but whether the accumulated residual

  E - D

is small enough to improve the budget.

## Budget test

Reconnect the new correction to the exact ledger

  oldBudget
  = higher
  + small carry
  + repeated large carry
  + Q.

Compare the new consumer with the 032 square-corrected consumer.

Outcome A requires a genuine gain under the existing project criterion: a universal strict budget result or a new unconditional prime-existence range beyond what the exact ledger already gives.

Recovering n=31 or other finite failures is useful evidence but remains Outcome B if the exact ledger already covers them.

## Independence and frontier caution

Using primality of small factor witnesses is acceptable only as a finite endpoint/factor condition, not as a disguised query of the target prime carrier Q.

If constructing the distinct witness requires complete factorization of every surviving q, then it has collapsed back to exact composite classification and should not be presented as an independent estimate.

Likewise, if semiprime witnesses leave a large higher-composite residual whose control is again a weighted short-interval sieve problem, state that frontier explicitly.

Do not import PNT, RH, or an unproved analytic estimate merely to force closure.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof strategy.

Keep the production surface small.

Prefer:

  collision-free composite carrier
  -> one certified lower mass D
  -> one corrected envelope / consumer
  -> obstruction and frontier audit

Do not build a large speculative hierarchy.

Do not predesign Instruction 034.

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

A collision-safe composite lower witness is formalized and yields a universal strict budget improvement or a genuinely new unconditional prime-existence range.

Outcome B:

A genuine new distinct-product lower witness and stronger envelope are formalized, but global closure is not obtained.

Outcome C:

The semiprime/distinct-product route collapses to exact factor classification, supplies negligible mass, or leaves the same weighted short-interval frontier unchanged.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-033.md

State:

- the collision-safe product carrier actually used,
- how product uniqueness is proved,
- how 49, 77 and 539 are handled,
- the certified lower composite mass D,
- the remaining error E-D,
- effect on n=29, n=31 and the retained larger anchors,
- effect on the exact 028-032 budget,
- diagnostics and counterexamples,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
