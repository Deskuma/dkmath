# Instruction 035 - Adaptive roughness cutoff and bulk residual closure

## Mission

Continue from Instruction 034.

Instruction 034 proved a collision-safe three-prime witness and made an explicit stopping decision against automatically adding four-, five-, and deeper factor-count carriers.

The remaining error is the weighted mass of surviving composites not covered by the semiprime or three-prime witnesses.

The next question is whether that entire higher-factor residual can be ruled out in bulk by choosing the finite wheel cutoff from endpoint geometry, rather than by enumerating deeper factor counts.

Do not assume in advance that this produces a useful budget theorem.

## Main research question

Can an adaptive finite prime basis force every surviving cofactor-window composite to have at most three prime factors counted with multiplicity?

The natural roughness mechanism is:

  every prime divisor of a survivor is greater than a cutoff c,

while every window value q satisfies an endpoint upper bound q <= B.

If four prime factors would imply

  (c+1)^4 > B,

then no four-or-more-factor survivor can exist.

Investigate whether this principle can be stated and proved cleanly in the existing 030-034 cofactor-window framework.

## Existing structure to audit first

Before adding new machinery, inspect and reuse:

- primeScalesUpTo and finite-prime-basis APIs,
- the 031 wheel-survivor / coprimality bridge,
- the 032 least-factor normal form,
- the 033 semiprime product carrier,
- the 034 ordered three-prime carrier,
- existing sqrt-roughness and fourth-power exclusion theorems, including the square-scale rough-factorization work.

There is already repository evidence that a sqrt-scale rough cutoff can make four prime factors too large for a square-scale interval.

Prefer a thin adapter to that structure over a new factor-depth theory.

## Candidate adaptive basis

A natural candidate is the finite basis containing all primes up to a scale such as Nat.sqrt n.

Do not force this exact cutoff if a cleaner or weaker sufficient cutoff emerges.

Any chosen basis must satisfy the existing safety condition that it does not delete desired singleton primes p > 2*n.

Prove the required basis coverage property explicitly.

For an initial prime basis, distinguish carefully between:

  r not in S

and

  every prime r <= c belongs to S.

The latter is what supports a numerical lower bound on surviving prime factors.

## Bulk exhaustion question

Suppose q is a surviving nonprime cofactor-window value.

Determine whether the adaptive roughness condition plus the window upper bound implies that q has exactly two or three prime factors counted with multiplicity.

If so, prove that q belongs to the existing semiprime or three-prime product image.

The desired result is an exhaustive statement of the form:

  surviving composite carrier
  = semiprime image union three-prime image

under explicit adaptive-basis hypotheses.

Use the existing proved disjointness of the two images when applicable.

Do not introduce a four-prime carrier merely to prove it is empty.

## Required regression points

Retain the fixed-wheel examples and show how the adaptive cutoff changes them.

In particular inspect:

- n=32, where 343 and 539 are already covered by the triple layer,
- n=69, where 2401=7^4 survives the fixed 30-wheel,
- n=210,297,1031 and 5000 from the retained diagnostics.

The n=69 case is important: the adaptive mechanism should explain structurally why the previous four-factor survivor is removed or becomes impossible, rather than merely recomputing its factorization.

## Exact-error consequence

If bulk exhaustion is proved, connect it to the 031-034 error coordinates.

Conceptually this should give

  D3 = E

for the adaptive basis,

and therefore remove the independent singleton-envelope excess entirely:

  corrected singleton envelope = Q.

Do not assume this identity before proving carrier exhaustion.

If the exact consequence has a different natural formulation, use it.

## Budget interpretation

After any exact residual closure, reconnect to

  oldBudget
  = higher
  + small carry
  + repeated large carry
  + Q.

The important question is then no longer whether the singleton approximation is sharp, but whether eliminating all approximation slack produces any genuinely new unconditional inequality.

If the adaptive construction merely recovers the exact old ledger, say so explicitly.

That is still a meaningful route-closing theorem: it would show that the 029-034 loss came from approximation and has now been completely removed, while the remaining obstruction lies in the exact ledger itself.

## Stopping criterion

Instruction 035 should decide whether the finite factor-depth campaign is finished.

If the adaptive roughness theorem exhausts all surviving composites with the already-built semiprime/triple layers, stop factor-depth development.

If it fails, identify the precise obstruction before proposing any deeper carrier.

Do not automatically continue to four-, five-, or higher-prime enumerators.

## Analytic / structural frontier

If exact singleton closure is achieved but the Legendre budget still does not close, identify the next frontier honestly.

Possible outcomes include:

- the exact old-budget inequality itself is the remaining problem;
- another non-singleton term, such as small carry, repeated carry, or higher-shell correction, is now the only available place for improvement;
- the route returns to a genuinely global prime-distribution or shell-structure question.

Do not import PNT, RH, or an unproved analytic estimate merely to force closure.

## Implementation policy

Work autonomously.

Choose theorem names, module placement, helper lemmas, diagnostics and proof strategy.

Keep the production surface small.

Prefer:

  adaptive basis / roughness bridge
  -> four-factor impossibility
  -> semiprime/triple exhaustion
  -> exact error consequence
  -> route-stopping interpretation

Do not build a general arbitrary-depth factorization hierarchy.

Do not predesign Instruction 036.

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

The adaptive roughness closure yields a universal strict budget result or a genuinely new unconditional prime-existence range beyond the exact ledger.

Outcome B:

A genuine bulk exhaustion / exact residual-closure theorem is formalized, but the resulting bound only recovers the exact ledger and does not globally close the prime-existence inequality.

Outcome C:

The adaptive cutoff cannot exhaust the higher-factor residual under the available endpoint geometry, or the proposed closure collapses into complete target factorization without a useful structural theorem.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-035.md

State:

- the adaptive basis or cutoff actually used,
- the proved lower bound on surviving prime factors,
- the four-factor impossibility theorem,
- whether semiprime/triple carriers exhaust all surviving composites,
- what happens to the n=69 four-factor regression,
- the exact relation between D3 and E,
- effect on the corrected singleton envelope,
- effect on the exact 028-034 budget,
- whether factor-depth development is now closed,
- diagnostics and counterexamples,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
