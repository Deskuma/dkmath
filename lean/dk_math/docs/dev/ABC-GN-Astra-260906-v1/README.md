# ABC–GN Astra Campaign 260906 v1

cid: 6a9d5951-68dc-83ee-b422-0b21f77bac4a

## Purpose

This directory is the mathematical restart point after the completed v0
fact-freezing campaign.

The v0 capstone is:

~~~text
DkMath.ABC.GNExcessCubicResearchFrontier
~~~

with the provider-free theorem:

~~~text
exp_GNExcessMassAt_sum_cubic_three_eighths_le_of_dyadicShellCardBounds
~~~

The deterministic Lean reduction is complete up to one explicit finite
arithmetic quantity:

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D
~~~

v1 does not begin by adding another production layer around that quantity.

v1 begins by doing new mathematics on the shell count itself.

## Branch

~~~text
branch: wip/ABC-GN-astra-260906-v1

predecessor:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

The v0 reports remain the authoritative record of the completed production
reduction.  In particular:

~~~text
v0/report-022.md
~~~

is the capstone status report.

## Exact frontier

For the canonical cubic value

~~~text
F(a) = a^2 + 3*a + 3 = GN 3 a 1,
~~~

a realized large repeated modulus M has a positive witness a with:

~~~text
1 <= a <= X

D <= M < 2D

X + 1 < M

M <= 3*(X+1)^2.
~~~

There is a canonical complement S:

~~~text
M*S = a^2 + 3*a + 3

1 <= S <= X

Squarefree S

Coprime M S.
~~~

The modulus is squarefull and has canonical square-cube coordinates:

~~~text
M = u^2*r^3

r = oddPart M

u = evenPart M / oddPart M

Squarefree r.
~~~

With

~~~text
T = r*S

d = evenPart M

y = 2*a+3,
~~~

production gives:

~~~text
y^2 + 3 = 4*T*d^2

Squarefree T

Coprime y d

gcd(y,T) divides 3.
~~~

The exceptional prime 3 is completely normalized into primitive sectors.

The paired orientation is also production-normalized:

~~~text
F(a) = GN 3 a 1
G(a) = GN 3 1 a

ordinary common support occurs only at 7;

the repeated parts are coprime;

the seven sector is exactly split modulo 49 into
  forward-deep,
  swap-deep,
  shallow-seven.
~~~

These are exact arithmetic facts, not density estimates.

## Research object

Conceptually set

~~~text
N_X(D)
=
GNExcessCubicRealizedLargeModulusShellCount X D
~~~

so that N_X(D) counts the distinct realized repeated moduli in the shell

~~~text
D <= M < 2D.
~~~

The capstone accepts any explicit bound

~~~text
N_X(2^k) <= B(k)
~~~

and propagates it to the cubic 3/8 excess-sum estimate.

Therefore the v1 problem is:

> Find a genuinely nontrivial upper bound for the number of distinct realized
> cubic repeated moduli in one dyadic shell.

## Research target

ASTRA-007 identified a sufficient target of rough shape:

~~~text
N_X(D)
<=
C_epsilon * X^(1+epsilon) / sqrt(D)
~~~

through the realized large range, with epsilon sufficiently small.

This is:

~~~text
RESEARCH TARGET — NOT PROVED
~~~

The exact exponent is not assumed.  A different shell estimate is welcome if
it is strong enough to improve the capstone dyadic moment.

## Regression barriers

Do not restart routes already falsified.

### Point-to-modulus injectivity

False.

Multiple witnesses can share one modulus.  Production regressions include
M=169 and M=8281.

### Fixed complement has bounded multiplicity

False.

There is an infinite strictly increasing Pell family with canonical
complement S=3.

### Local paired depth competition

False.

Independent exact depths can be forced in opposite orientations.

### Coprime repeated parts imply one is small

False.

Both repeated parts can be arbitrarily large in absolute size while remaining
coprime.

### Hensel uniqueness implies global rarity

False as a general inference.

Simple roots lift to arbitrary finite depth.

### Mod-49 state normalization proves density

False.

The forward-deep / swap-deep / shallow-seven split is local arithmetic only.

## Research discipline

The first v1 pass is pure mathematics.

Do not begin by creating a new production DkMath module.

Allowed:

~~~text
exact derivations
scratch Lean for delicate identities
numerical falsification
literature research when genuinely useful
~~~

Required status labels:

~~~text
PRODUCTION-PROVED
SCRATCH-PROVED
NUMERIC
OPEN
DEAD
~~~

The desired result is not a long brainstorm.

The desired result is:

~~~text
many plausible routes
->
one or two surviving mechanisms
->
one precise quantitative theorem target.
~~~

## Model roles

### Sol

First attacker.

Reconstruct the shell-count problem, derive candidate mechanisms, and prune
branches aggressively.

### Astra

Second-pass artillery / referee.

Use Astra only after Sol has isolated a small set of serious candidate routes.
Astra should attack proof gaps, hidden multiplicity, and exponent loss rather
than reconstruct the whole campaign.

### Luna / implementation model

Do not use for new hard mathematics.

Return to production implementation only after a genuinely new theorem has
survived mathematical review.

## Files

- ROADMAP.md — v1 mathematical research and production-gate program.
- instruction-000.md — SOL shell-count exploration.
- report-000.md — SOL-000 research result.
- instruction-001.md — ASTRA adversarial review.
- report-001.md — ASTRA-001 validated fiber theorem and research frontier.
- instruction-002.md — LUNA production freeze of shell-fiber uniqueness.

## Current production gate

ASTRA-001 validated a new deterministic theorem in scratch Lean:

~~~text
fixed (T,r) + one dyadic shell
=>
at most one witness.
~~~

It also validated shell-local injectivity of:

~~~text
a |-> (r,S).
~~~

These facts are now approved for productionization by LUNA-002.

The following remain research-only:

~~~text
Helfgott-Venkatesh specialization
31/24 + epsilon moment estimate
balanced-box power saving
ABC closure.
~~~

## Status

~~~text
v0 production reduction:
  COMPLETE / PAUSED

v1 Sol research:
  COMPLETE / Outcome B

v1 Astra review:
  COMPLETE / Outcome B

v1 LUNA production freeze:
  ACTIVE / instruction-002

Astra:
  PAUSED UNTIL RECHARGE

ABC:
  NOT PROVED

current research frontier after production freeze:
  balanced-box represented-pair saving
~~~
