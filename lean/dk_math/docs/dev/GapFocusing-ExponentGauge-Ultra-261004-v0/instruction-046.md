# Instruction 046 - Allocation threshold branch selector

## Mission

Continue from Instruction 045.

Instruction 045 reduced the full internal depth-four reconstruction obligation to the OR of two matched scalar receivers over the same source core M.

Both branches use positive coprime factors r,s with

  M = r*s,

the same large scale

  D = 7^27*r^49,

and the same target

  7*s^49.

They differ only in the residual polynomial:

  GN branch:
    GN 7 D u = 7*s^49,

  right-hand-side branch:
    alternatingCyclotomicSeven u (D-u) = 7*s^49.

The next task is to exploit the fact that these two residuals lie on opposite sides of the exact threshold D^6.

Do not start recursive descent.

## Main observation to formalize

For the GN branch, u is positive. The explicit degree-seven GN expansion should imply

  D^6 < GN 7 D u.

Therefore any GN receiver satisfies

  D^6 < 7*s^49.

For the right-hand-side branch, write v=D-u. Its receiver has

  0<u<D,
  0<v,
  D=u+v.

Because u and v are both strictly between 0 and D,

  u^7 + v^7 < D^7.

Using

  D * alternatingCyclotomicSeven u v = u^7 + v^7

and D>0, derive

  alternatingCyclotomicSeven u v < D^6.

Therefore any right-hand-side receiver satisfies

  7*s^49 < D^6.

Prefer elementary natural-number inequalities over real analysis.

## Allocation threshold

Substitute

  D = 7^27*r^49

and

  M = r*s.

The desired exact allocation inequalities are

  GN branch:
    7^161 * r^343 < M^49,

  right-hand-side branch:
    M^49 < 7^161 * r^343.

Check all exponent arithmetic in Lean.

Do not replace these by approximate real roots unless useful only for diagnostics.

## Branch selector

For the actual source core M, seven does not divide M.

Any factor r of M used by either nested receiver is therefore also a seven-unit.

Hence

  M^49 = 7^161*r^343

should be impossible, since the right side is divisible by seven while the left side is not.

Exploit this to obtain a strict branch selector for each fixed factor allocation r:

- if
    7^161*r^343 < M^49,
  the right-hand-side receiver at this r is impossible;

- if
    M^49 < 7^161*r^343,
  the GN receiver at this r is impossible.

A useful theorem may state that one fixed allocation cannot support both branches.

Better still, expose the combined reconstruction condition as a finite divisor search in which each divisor allocation is routed to at most one residual equation by this threshold comparison.

Do not claim that the global OR is resolved: different divisors r may lie on different sides.

## Common coarse size filter

Also investigate the report-045 common size estimate.

For the GN branch, the stronger inequality already gives

  D^6 < 7*s^49.

For the right-hand-side branch, use a proved finite-power inequality such as

  (u+v)^7 <= 64*(u^7+v^7)

to obtain

  D^6 <= 64*7*s^49.

From either branch, prove a simple source-supported lower bound such as

  s > 7^3*r^6

if the arithmetic is sufficient.

Equivalently, using M=r*s,

  M > 7^3*r^7.

In particular any reconstruction would imply

  343 < M.

This is a coarse corollary; the exact threshold selector above is the primary target.

If a stronger simple integer constant is essentially free, it may be recorded, but do not turn this checkpoint into numerical constant optimization.

## Divisor-supported reconstruction API

The GN branch already has a divisor-supported form from Instruction 044.

Add the analogous right-hand-side divisor support if needed, and then expose one combined finite allocation theorem for positive source core M:

  reconstruction
    iff
  exists r in M.divisors,
    let s := M/r;
    Nat.Coprime r s
    and
    (
      thresholdGN(M,r) and exact GN scalar condition
      or
      thresholdRHS(M,r) and exact alternating scalar condition
    ).

The exact Lean shape is open.

The important point is that the threshold comparison should route an allocation before solving the scalar endpoint equation.

Do not encode the branch choice by testing the residual equation itself.

## Source relation audit

The current inner-coordinate split also proves

  |innerRoot.snd| *
  |seventhPowerSndCore(innerRoot)|
    =
  7^4 * (verticalGapRoot*compensationRoot)^7.

Together with

  |innerRoot.snd| = 7^4*M^7

and the existing seventh-power split of the core, this should yield a source relation of the form

  M * N = verticalGapRoot * compensationRoot

for some positive complementary seventh-root N.

Formalize this only if it is thin and useful.

Then record whether the new lower bound on M produces any nontrivial restriction on the already-existing outer roots.

Do not invent an upper bound for M if none is present.

## Optional alternating uniqueness

Instruction 045 left ordered endpoint uniqueness open.

This is secondary.

If the threshold/divisor work is short, test the fixed-sum polynomial identity

  alt = D^6 - 7*D^4*t + 14*D^2*t^2 - 7*t^3,
  t=u*v,

on the ordered half u<=D-u.

A clean monotonicity theorem giving at most one ordered endpoint per allocation is useful.

Do not let this optional proof dominate the checkpoint.

## Circularity guard

The following do not count as progress:

- defining the threshold from the truth value of a receiver;
- numerically approximating 7^(161/49) and using that as a proof premise;
- assuming reconstruction to choose the favorable branch globally;
- replacing exact scalar equations by congruences;
- using matching seven-adic depth to identify coordinates;
- building a brute-force endpoint search instead of proving the threshold routing.

## Success interpretation

The ideal result is not yet FLT7.

It is a theorem that the two matched receiver branches occupy disjoint multiplicative regions of the same source factor allocations.

This would change the reconstruction problem from

  for each allocation, test two scalar equations

to

  for each allocation, the arithmetic threshold selects at most one scalar equation.

The coarse corollary

  reconstruction -> 343 < M

would also be a genuine source-level exclusion for small cores.

## Outcome classification

Outcome A:

The threshold selector, combined with existing source constraints, eliminates every supported allocation or otherwise resolves the reconstruction obligation, yielding one-step descent or terminal exclusion.

Outcome B:

The exact opposite-side inequalities, allocation threshold selector, and a materially thinner divisor-supported reconstruction condition are formalized, but some allocations remain unresolved.

Outcome C:

The threshold comparison fails, cannot be connected to the exact receivers, or gives no structural improvement beyond restating existing equations.

All outcomes are acceptable.

## Validation

Use:

- focused build;
- FLT Seven facade build;
- root build when appropriate;
- axiom audit for all new public declarations.

Keep Legendre parked.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-046.md

State:

- the exact GN lower comparison with D^6;
- the exact alternating upper comparison with D^6;
- the derived inequalities in M and r;
- whether equality at the threshold is excluded;
- the resulting per-allocation branch selector;
- the combined divisor-supported reconstruction theorem;
- any common coarse lower bound such as M>343;
- any useful source relation for M to existing outer roots;
- any ordered endpoint uniqueness theorem;
- whether reconstruction, exclusion, or one-step descent is obtained;
- build/axiom status;
- Outcome A/B/C;
- the next natural frontier.
