# Instruction 041 - Active repeated-base aggregate bound

## Mission

Continue from Instruction 040.

Instruction 040 proved a genuine repeated-large phase compression by testing only the first eligible repeated power of each prime base.

The resulting envelope is much smaller than the full nonprime band and repairs all retained sampled correction failures, including n=69 and n=297, while preserving the long ten-exponent base-2 regression at n=2896.

Do not reopen the central-binomial compensation route or singleton factor-depth route.

The next question is whether the repeated-phase envelope itself admits an independent aggregate bound at the level of active prime bases.

A mere reindexing of the exact envelope is not sufficient progress.

## Exact starting point

For each prime base p define

  a0(n,p) = max(2, Nat.log p (2*n) + 1).

Instruction 040 tests only the first eligible repeated power p^a0.

If that first power is inactive, the entire later exponent chain is excluded.

If it is active, the current envelope retains every exponent

  a0 <= a <= Nat.log p (n^2)

with weight log p for each exponent.

Thus the natural base contribution is

  intervalLength(n,p) * log p.

The present label-based carrier is already proved correct.

## Main research question

Can the Instruction 040 envelope be bounded by a simpler independent sum over active bases, and can the total active-base contribution itself be bounded from endpoint geometry?

The desired progress is not just

  R_phase = sum over active bases of exact interval weights.

That equality is useful infrastructure but by itself is only a reindexing.

Seek an actual aggregate inequality that discards information while remaining strictly sharper than the old nonprime band and quantitatively meaningful for the total correction budget.

## First step: base-sum form

Formalize a thin base-sum receiver if needed:

  R_phase(n)
    = sum over eligible active prime bases p
        intervalLength(n,p) * log p.

Preserve exponent multiplicity exactly.

The n=2896 base-2 contribution must still be ten copies of log 2.

Do not quotient by shell target and do not replace a full exponent interval by one base log.

## Structural split

Investigate the natural split according to whether

  p^2 <= 2*n

or

  2*n < p^2.

For the second region, the first repeated exponent is exactly 2.

Hence activity is the single square-power carry condition

  carryBit(n,p^2)=1.

Using the existing large-gap / next-multiple packet, this is equivalent to the existence of the unique shell multiple

  n^2 < k*p^2 <= n^2+2*n

with

  k = n^2 / p^2 + 1.

This square-divisor / quotient geometry is the main object to investigate.

## Large-square-base region

For active p with p^2>2*n, seek an independent aggregate bound on their weighted contribution.

Possible useful forms include:

- a bound on the number or weighted mass of active square bases;
- an injective or bounded-multiplicity routing to quotient values k;
- endpoint windows for p obtained from
    n^2/k < p^2 <= (n^2+2*n)/k;
- a square-divisor count for shell integers;
- a finite product inequality using only endpoint data;
- a bound on
    sum active intervalLength(n,p)*log p
  that does not enumerate exact later carry bits.

Do not force one representation if another is cleaner.

## Small-base region

For p^2<=2*n, a0 may exceed 2 and long exponent chains are possible.

Use the existing exponent-interval formula and any safe global prime-power estimate that preserves multiplicity.

A coarse but genuinely sublinear or otherwise controlled contribution is acceptable if it combines well with the large-square-base estimate.

Do not assume uniformly bounded exponent length.

## Required regressions

Retain at least:

- n=69, where Instruction 040 reduced repeated budget about 68.41 -> 14.09;
- n=297;
- n=1031;
- n=2896 with the ten consecutive base-2 exponents;
- n=5000.

Also preserve a small anchor with empty or trivial repeated carry if useful.

Any proposed base-count or quotient multiplicity theorem must survive these cases.

## Quantitative target

If an independent aggregate repeated bound R_base(n) is proved, require

  repeatedCarryMass(n)
    <= R_phase(n)
    <= R_base(n)

or another correct orientation with a clearly stronger usable envelope.

The new bound should be compared with Instruction 040 numerically and structurally.

If it is looser than R_phase but much simpler, it must still be strong enough to be useful in the total budget.

If it is just a restatement of R_phase, classify that honestly.

## Combined correction budget

When justified, combine the new repeated estimate with:

- the strongest proved small-carry phase bound from Instruction 037;
- the existing reciprocal higher-correction bound;
- the exact Q term from Instruction 035.

Expose one conditional provider only if the resulting budget is genuinely useful:

  Q + B041(n) < log(cell)
    -> exists prime in SquareCell n.

Do not assume the unresolved central-binomial conjecture.

## Route-stopping test

Instruction 040 already gives positive diagnostic correction margins at all retained sampled anchors.

Therefore this checkpoint is also a stopping test for further correction refinement.

If no nontrivial aggregate active-base estimate is obtained beyond reindexing or a weak square-divisor count, stop refining the correction terms.

In that case identify the remaining frontier as the independent control of Q / the exact total strict criterion, rather than adding further local repeated-carry heuristics.

## Circularity guard

The following do not count as progress:

- summing over the exact active-base set and calling that a new bound;
- using exact later carry bits after the first-power gate;
- using Q, shell prime birth, or oldBudget strictness;
- losing exponent multiplicity;
- importing an unproved analytic prime-distribution estimate;
- creating an arbitrary hierarchy of square-divisor subcases.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

Diagnostics are evidence, not proof premises.

## Outcome classification

Outcome A:

An aggregate active-base estimate, together with existing production results, yields a universal strict budget theorem or a genuinely new unconditional prime-existence range.

Outcome B:

A genuine independent active-base / square-divisor bound is formalized and improves or substantially simplifies the repeated correction, but universal closure is not obtained.

Outcome C:

Only a reindexing is obtained, or the aggregate route reduces to another uncontrolled square-divisor / short-interval problem without a useful independent bound.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-041.md

State:

- the base-sum representation actually used;
- the large-square-base and small-base split;
- the square-divisor / quotient geometry proved;
- the strongest independent active-base estimate obtained;
- how n=69 and n=2896 are handled;
- comparison with Instruction 040;
- effect on the combined correction budget;
- whether correction refinement should now stop;
- axiom/build status;
- Outcome A/B/C;
- the next natural frontier suggested by the result.
