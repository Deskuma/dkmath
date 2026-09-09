# ROADMAP — ABC–GN Astra Campaign 260906 v1

## 0. Strategic reset

v1 begins after the successful v0 capstone.

The previous phase answered:

> What deterministic structure can be extracted and formalized before a new
> global counting theorem is required?

Answer:

~~~text
essentially all currently known deterministic structure has been frozen.
~~~

The new question is narrower:

> How many distinct realized cubic repeated moduli can occur in one dyadic
> shell?

The central object is:

~~~text
N_X(D)
=
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

Do not add more bookkeeping layers around N_X(D).

Attack N_X(D).

---

## 1. Fixed production facts

Treat the following as infrastructure.

### 1.1 Capstone reduction

The v0 capstone gives:

~~~text
explicit shell-card bounds
=>
cubic 3/8 excess-sum bound.
~~~

Therefore any useful new shell-count theorem has an immediate downstream
consumer.

### 1.2 Canonical witness packet

A represented shell modulus M has a positive witness a with:

~~~text
1 <= a <= X

D <= M < 2D

X + 1 < M

M*S = a^2 + 3*a + 3

1 <= S <= X

Squarefree S

Coprime M S.
~~~

### 1.3 Square-cube packet

~~~text
M = u^2*r^3

r = oddPart M

u = evenPart M / oddPart M

Squarefree r.
~~~

### 1.4 Pell/conic packet

With

~~~text
T = r*S

d = evenPart M

y = 2*a+3,
~~~

production gives:

~~~text
Squarefree T

y^2 + 3 = 4*T*d^2

Coprime y d

gcd(y,T) divides 3.
~~~

The exceptional 3-sector is completely normalized.

### 1.5 Paired orientation packet

For F(a)=GN 3 a 1 and G(a)=GN 3 1 a:

~~~text
ordinary overlap only at 7;

repeated parts coprime;

deep 7-support occurs exactly in mod-49 residues 29 or 22;

the remaining seven-sector is shallow.
~~~

Do not confuse these local facts with a counting theorem.

---

## 2. Hard regression barriers

Every candidate route must be checked against these facts.

### R1 — modulus collisions exist

a -> M is not injective.

Therefore any argument that counts witnesses by moduli must explicitly control
fiber multiplicity.

### R2 — fixed complement can have infinitely many witnesses

S=3 occurs along an infinite Pell family.

Therefore a fixed-S O(1) witness bound is false.

### R3 — independent deep orientation lifts exist

Paired local depth competition cannot be used as a universal obstruction.

### R4 — coprime repeated parts may both be huge

No absolute-size dichotomy follows from paired coprimality.

### R5 — Hensel depth is not rare by itself

Local root uniqueness does not automatically produce global sparsity.

### R6 — mod-49 state normalization is not an asymptotic estimate

Residue classification alone does not solve the shell count.

---

## 3. Phase S0 — Sol reconstruction

Status: start here.

Goal:

Reconstruct N_X(D) as a pure number-theoretic incidence problem using only
production facts.

Required output:

~~~text
- exact mathematical restatement of shell membership;
- best immediate/trivial upper bounds;
- exact place where each trivial bound loses;
- comparison of the most rigid coordinate systems.
~~~

Candidate coordinates:

~~~text
(a,M)

(M,S)

(r,u,S)

(T,d)

paired forward/swap coordinates.
~~~

Do not assume one coordinate system is best.

---

## 4. Phase S1 — branch generation and immediate falsification

Generate several genuinely different mechanisms, then kill weak ones quickly.

### A — square-cube shell geometry

Use:

~~~text
D <= u^2*r^3 < 2D

r squarefree.
~~~

Questions:

- for fixed r, how many u are shell-admissible?
- what is the useful range of r?
- does realization M | a^2+3a+3 improve generic squarefull counting?
- can r | d or q == 1 mod 3 support produce an extra saving?

Danger:

Counting all squarefull integers in the shell is already known to be too weak.

### B — product incidence

Use:

~~~text
M*S = a^2 + 3*a + 3

M ~ D

S <= X.
~~~

Questions:

- can distinct M be counted by lattice/product incidences?
- can dyadic slicing in S produce a true average multiplicity estimate?
- can fixed-M spacing combine with shell geometry?
- is there a divisor-switching or energy argument that avoids false
  injectivity?

Mandatory warning:

~~~text
fixed S can have infinitely many witnesses;
a -> M is not injective.
~~~

### C — Pell/conic incidence

Use:

~~~text
y^2 + 3 = 4*T*d^2

T squarefree

T = r*S.
~~~

Questions:

- what is the actual shell range of T and d?
- for fixed T, does D <= M < 2D cut a Pell orbit into a short segment?
- does r | d add a restriction absent from generic Pell counting?
- can average-over-T bounds beat worst-case multiplicity?
- can Eisenstein factorization help?

Mandatory regression:

~~~text
the S=3 Pell family.
~~~

### D — squarefree kernel T=r*S

Use:

~~~text
r squarefree

S squarefree

Coprime r S

T=r*S

r^3 <= M < 2D

S <= X.
~~~

Questions:

- is the effective T-space substantially smaller than the naive range?
- can (r,S) be counted by a hyperbola-type argument?
- does the requirement that T support a conic point with d carrying r give
  a genuine sieve?
- can q == 1 mod 3 support of r be used quantitatively?

### E — paired orientation

Use paired facts only if they produce a genuinely global gain.

Questions:

- does a large forward repeated modulus force a constrained swap state?
- does MF*MG | 3*(a+1)^4+a^2 help count forward shell moduli?
- can the exact mod-49 state split isolate a smaller exceptional family?
- is there an average relation between the two square-cube cores?

Mandatory regression:

~~~text
MF and MG can both be arbitrarily large in absolute size.
~~~

Any useful paired theorem must be height-relative, averaged, or
incidence-based.

---

## 5. Phase S2 — quantitative benchmark

Before accepting any route, derive its explicit shell-count consequence.

The rough ASTRA-007 target is:

~~~text
N_X(D)
<=
C_epsilon * X^(1+epsilon) / sqrt(D).
~~~

Do not treat this form as sacred.

For each surviving route derive something explicit such as:

~~~text
N_X(D) <= X^alpha * D^beta * log(X)^gamma.
~~~

Then insert the shell weight:

~~~text
shell contribution
~
N_X(D) * D^(3/8).
~~~

Classify the resulting top-shell behavior as:

~~~text
sublinear in X
linear in X
superlinear in X.
~~~

A route is not promising until this exponent check is done.

---

## 6. Phase S3 — multiplicity audit

Any proposed shell-count argument must state which map is being counted:

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
~~~

Do not hide multiplicity inside Finset.image notation.

---

## 7. Phase S4 — arithmetic falsification

For every serious candidate theorem:

1. test small and medium X numerically;
2. target collision moduli 169 and 8281;
3. target the S=3 Pell family;
4. target paired exact-depth CRT families;
5. target all three mod-49 seven states.

The purpose is not numerical proof.

The purpose is cheap falsification.

---

## 8. Phase S5 — theorem isolation

A successful Sol pass ends with one of:

### Outcome A — strong candidate

A precise shell-count theorem with a plausible proof route and no known
regression conflict.

### Outcome B — meaningful partial mechanism

A quantitatively useful theorem in a regime such as:

~~~text
large D

small cube-core

large complement

one arithmetic sector.
~~~

### Outcome C — obstruction

A convincing reason why all obvious coordinate attacks remain insufficient,
plus the exact missing theorem.

Outcome C is acceptable.

Do not manufacture a production task merely to continue.

---

## 9. Phase A0 — Astra review

Do not enter until Sol reduces the candidate set to one or two serious routes.

Astra's job:

~~~text
- attack proof gaps;
- search for hidden counterfamilies;
- compare exponents;
- identify the weakest sufficient statement;
- replace an unnecessarily strong route with a cleaner one when possible.
~~~

Do not spend Astra budget reconstructing v0.

Provide Astra the Sol report and the v0 capstone facts.

---

## 10. Production gate

Return to Lean production only if a genuinely new theorem survives review.

Before implementation require:

~~~text
precise theorem statement

counterexample audit passed

dependency on production facts identified

quantitative gain demonstrated

no abc_main_axiom

no provider assumption.
~~~

Until then:

~~~text
NO LUNA production sequence.
~~~

---

## 11. Success criterion

The desired bridge is:

~~~text
new arithmetic incidence theorem
->
nontrivial N_X(D) bound
->
capstone dyadic moment bound
->
ABC-side progress.
~~~

The first arrow is the only current research target.

---

## 12. Current status

~~~text
v0 deterministic reduction:
  COMPLETE

v1 Sol mathematical attack:
  READY

Astra review:
  WAITING FOR SOL CANDIDATES

production implementation:
  PAUSED

ABC:
  NOT PROVED
~~~
