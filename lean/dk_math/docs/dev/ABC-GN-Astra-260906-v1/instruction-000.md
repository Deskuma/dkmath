# instruction-000 — SOL full-reasoning attack on the cubic realized shell count

## Role

Act as a research mathematician.

This is not a Lean implementation task.

This is the first pure-mathematics pass on the v1 ABC–GN frontier.

Use full reasoning.

The target is the finite arithmetic quantity

~~~text
N_X(D)
=
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

Do not spend the pass polishing already-proved production facts.

Do not create a provider, conjecture wrapper, axiom, or ABC endpoint.

---

## Repository / branch

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v1

v0:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/

v1:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read first:

~~~text
v1/README.md
v1/ROADMAP.md

v0/report-022.md
v0/report-021.md
v0/report-020.md
v0/report-019.md
v0/report-018.md
v0/report-017.md
v0/report-016.md
v0/report-015.md
v0/report-014.md
v0/report-013.md
v0/report-012.md
v0/report-011.md
v0/report-010.md
v0/report-009.md
v0/report-008.md
v0/report-007.md
~~~

Inspect current production source whenever theorem details matter.

The capstone entry point is:

~~~text
DkMath/ABC/GNExcessCubicResearchFrontier.lean
~~~

---

## Exact frontier

The v0 capstone proves:

~~~text
explicit bounds on realized dyadic shell counts
=>
the current cubic 3/8 excess-sum bound.
~~~

The remaining open arithmetic quantity is exactly:

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

The mathematical task is to obtain a genuinely nontrivial upper bound for this
quantity.

---

## Canonical mathematical restatement

A modulus M counted by N_X(D) is a distinct realized repeated modulus arising
from some positive witness a satisfying:

~~~text
1 <= a <= X

D <= M < 2D

X + 1 < M

M <= 3*(X+1)^2.
~~~

For the same witness there is a canonical complement S:

~~~text
M*S = a^2 + 3*a + 3

1 <= S <= X

Squarefree S

Coprime M S.
~~~

M is squarefull and has canonical square-cube coordinates:

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

y = 2*a + 3,
~~~

production gives:

~~~text
y^2 + 3 = 4*T*d^2

Squarefree T

Coprime y d

gcd(y,T) divides 3.
~~~

The exceptional prime 3 is completely normalized.

Paired cubic orientation facts are also production-proved:

~~~text
F(a)=GN 3 a 1
G(a)=GN 3 1 a

ordinary overlap only at prime 7;

the repeated parts are coprime;

the seven sector has exact mod-49 states:
  forward-deep: 29
  swap-deep:    22
  shallow-seven: the remaining seven-sector residues.
~~~

Use paired data only if it creates a genuinely global gain.

---

## Required research objective

Find the strongest plausible route to a nontrivial bound for N_X(D).

ASTRA-007 identified a sufficient rough target:

~~~text
N_X(D)
<=
C_epsilon * X^(1+epsilon) / sqrt(D)
~~~

for suitable small epsilon in the realized large range.

This exact form is not mandatory.

A different explicit bound is acceptable if its dyadic contribution beats the
current trivial exponent strongly enough to matter at the capstone.

---

## Task 1 — reconstruct the baseline

Before proposing new theorems, derive from the current facts:

1. the best immediate/trivial upper bounds for N_X(D);
2. the corresponding dyadic moment contribution;
3. exactly where those bounds lose.

Do not merely quote old summaries.

Reconstruct the exponent loss yourself.

The research must begin with a quantitative benchmark.

---

## Task 2 — attack several genuinely different coordinate systems

Generate branches, but prune aggressively.

### Route A — square-cube shell geometry

Use:

~~~text
D <= u^2*r^3 < 2D

r squarefree.
~~~

Investigate:

- for fixed r, the length of the admissible u interval;
- the actual range of r;
- whether realization into a^2+3a+3 reduces generic squarefull counts;
- whether r divides d or prime support q == 1 mod 3 gives an extra saving;
- whether r is the right main summation variable.

Do not stop at generic squarefull counting.

That route is already too weak unless realization gives a further gain.

### Route B — product incidence M*S = F(a)

Use:

~~~text
M*S = a^2 + 3*a + 3

M ~ D

S <= X

Squarefree S

Coprime M S.
~~~

Investigate:

- divisor switching;
- dyadic slicing in S;
- lattice or hyperbola incidence;
- additive/multiplicative energy formulations;
- fixed-M spacing;
- average rather than worst-case multiplicity.

Mandatory warnings:

~~~text
a -> M is not injective;

fixed S can support infinitely many witnesses.
~~~

Any proposed count must explicitly survive both facts.

### Route C — Pell/conic incidence

Use:

~~~text
y^2 + 3 = 4*T*d^2

T squarefree

T = r*S.
~~~

Investigate:

- the shell-imposed range of T and d;
- whether fixed T intersects a shell in a short segment of a Pell orbit;
- whether r divides d gives a restriction absent from generic Pell equations;
- average-over-T bounds;
- primitive conic counting after the 3-sector normalization;
- Eisenstein-integer factorization if useful.

Mandatory regression:

~~~text
the S=3 Pell family.
~~~

Do not assert a uniform O(1) fixed-T multiplicity without proving the shell or
height mechanism that forces it.

### Route D — squarefree kernel T=r*S

Use:

~~~text
r squarefree

S squarefree

Coprime r S

T=r*S

r^3 <= M < 2D

S <= X.
~~~

Investigate:

- the effective size of the represented T-space;
- hyperbola counts for (r,S);
- whether requiring a conic point with d carrying r gives a sieve;
- whether q == 1 mod 3 support of r can be used quantitatively.

Do not turn support congruence into a density claim without a proof.

### Route E — paired orientation

Use exact paired facts only if they improve the shell count.

Investigate:

- constraints on the swap orientation created by a large forward M;
- whether MF*MG dividing 3*(a+1)^4+a^2 yields a useful incidence bound;
- whether the exact mod-49 state split isolates a smaller exceptional family;
- whether the two square-cube cores interact on average.

Mandatory regression:

~~~text
MF and MG may both be arbitrarily large in absolute size.
~~~

Any useful theorem must therefore be height-relative, averaged, or
incidence-based.

---

## Task 3 — mandatory dead-end checks

Every strong candidate must be tested against:

~~~text
1. modulus collisions:
   M=169 at multiple witnesses;
   M=8281 at four known witnesses.

2. the infinite complement-3 Pell family.

3. independent exact paired depths at 7 and 13.

4. arbitrarily large coprime paired repeated parts.

5. arbitrary finite Hensel lifting.

6. all three mod-49 seven states.
~~~

If a candidate contradicts one of these, mark it DEAD immediately.

---

## Task 4 — quantitative consequence

For every surviving route, derive an explicit shell-count consequence.

Preferred form:

~~~text
N_X(D)
<=
X^alpha * D^beta * log(X)^gamma
~~~

or another comparably explicit finite estimate.

Then insert the capstone shell weight:

~~~text
N_X(D) * D^(3/8).
~~~

Explain the top-shell exponent in X.

Classify it as:

~~~text
sublinear

linear

superlinear.
~~~

Do not call a route promising until this propagation is done.

---

## Task 5 — multiplicity audit

For every counting argument, state explicitly which map is being counted.

Candidates:

~~~text
a -> M

a -> (M,S)

a -> T

(M,S) -> T

a -> paired coordinates.
~~~

For each map answer:

~~~text
injective?

finite-to-one?

known unbounded multiplicity?

what exact theorem controls the multiplicity?

what shell/height restriction is actually used?
~~~

Do not hide multiplicity in image notation.

---

## Task 6 — falsification experiments

Numerical work is encouraged only for diagnosis.

For each serious candidate:

- scan small and medium X;
- target known collision moduli;
- target the S=3 Pell family;
- target paired exact-depth CRT families;
- separate all three mod-49 seven states.

Use the experiments to kill false conjectures early.

Do not treat numerical survival as proof.

---

## Task 7 — external mathematics when useful

If a candidate reaches known work on:

~~~text
squarefull values of quadratics

Pell solution counts

integral points on conics

binary quadratic forms

Eisenstein integers

squarefree kernels

divisor problems

determinant/incidence methods
~~~

research the literature/web if it materially advances the analysis.

When using external results:

~~~text
state exact hypotheses;

separate them from DkMath production facts;

check unconditionality;

do not use ABC-conditional results;

check whether the quantitative exponent is actually strong enough.
~~~

---

## Do not implement production Lean

During SOL-000:

~~~text
DO NOT create a new production DkMath module.

DO NOT update DkMath/ABC.lean.

DO NOT add a provider.

DO NOT add a conjecture constant.

DO NOT add an axiom.

DO NOT claim ABC.
~~~

Scratch Lean is allowed only to verify a delicate exact identity.

---

## Required output

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-000.md
~~~

Title:

~~~text
# SOL-000 — cubic realized shell-count attack
~~~

The report must contain:

### 1. Exact mathematical restatement

Write N_X(D) and shell membership in ordinary mathematical notation.

### 2. Baseline bounds

Derive the current trivial bounds and explain quantitatively why they fail.

### 3. Route ledger

For Routes A–E, clearly label findings as:

~~~text
PRODUCTION-PROVED

SCRATCH-PROVED

NUMERIC

OPEN

DEAD

WEAK

SURVIVES

PROMISING.
~~~

### 4. Branch pruning

Explain why dead/weak routes are discarded.

### 5. Best candidate theorem

State the weakest serious theorem you currently believe can yield a useful
shell-count gain.

It must be precise enough for Astra to review.

### 6. Quantitative exponent propagation

Show exactly what the candidate theorem gives after multiplication by
D^(3/8) and dyadic summation.

### 7. Counterexample audit

Check every mandatory regression.

### 8. Mathematical proof plan

Give a proof decomposition.

Do not give a Lean implementation plan yet.

### 9. ASTRA REVIEW TARGET

Include a short section with only the strongest one or two surviving routes
and the precise issues where independent high-power review is needed.

### 10. Verdict

Use one of:

~~~text
Outcome A — strong new theorem candidate

Outcome B — meaningful partial mechanism

Outcome C — current routes insufficient
~~~

Outcome C is acceptable.

---

## Success criterion

A successful pass is not a long brainstorm.

It is:

~~~text
many plausible branches
->
one or two serious routes
->
one precise theorem target
->
a quantitative reason that theorem matters.
~~~

If no route survives, state that clearly and identify the missing concept.

Do not manufacture a candidate to keep the campaign moving.

---

## Stop condition

Stop after report-000.md is complete.

Do not create instruction-001 automatically.

The report will first be reviewed by Sol/human.

Only then should the strongest surviving route be handed to Astra for
adversarial review.
