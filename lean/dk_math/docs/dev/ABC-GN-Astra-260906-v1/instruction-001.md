# instruction-001 — ASTRA adversarial review of the norm-minus-three shell mechanism

## Role

Act as an adversarial research referee with maximum mathematical effort.

This is not a production Lean implementation task.

SOL-000 has completed the first full-reasoning attack on the v1 shell-count
frontier and returned:

~~~text
Outcome B — meaningful partial mechanism.
~~~

Your job is now to stress-test the strongest surviving mechanism, not to
reconstruct the whole v0 campaign.

The two review targets are:

~~~text
A. fixed-(T,r) dyadic shell fiber <= 2;

B. whether represented (r,S) pairs admit a further power saving beyond the
   rectangular box count.
~~~

Do not claim ABC.

---

## Repository / branch

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v1

v1:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/

v0:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read first:

~~~text
v1/README.md
v1/ROADMAP.md
v1/report-000.md
v1/scratch-000.lean
v1/validation-000.txt

v0/report-022.md
v0/report-015.md
v0/report-014.md
v0/report-013.md
v0/report-009.md
v0/report-008.md
v0/report-007.md
~~~

Inspect production source only where theorem details matter.

Do not spend the review budget re-reading unrelated ABC modules.

---

# Review target A — dyadic norm-minus-three fiber theorem

SOL-000 proposes the following OPEN theorem.

For a shell witness a, define production coordinates

~~~text
M = repeated modulus
S = complement
r = oddPart M
T = r*S
d = evenPart M
y = 2*a+3.
~~~

Production gives:

~~~text
M = r*d^2

y^2 + 3 = 4*T*d^2

T squarefree

d > 0

y > 0.
~~~

For fixed X,D,T,r define the shell fiber conceptually by

~~~text
P_X,D(T,r)
=
{
  a :
  1 <= a <= X,
  X+1 < M(a),
  D <= M(a) < 2D,
  T(a)=T,
  r(a)=r
}.
~~~

The candidate theorem is:

~~~text
# P_X,D(T,r) <= 2.
~~~

The proposed proof is by the quadratic norm equation.

For T>1 set

~~~text
K = Q(sqrt(T))

alpha = y + 2*d*sqrt(T).
~~~

Then

~~~text
Norm(alpha) = -3.
~~~

Since alpha is an algebraic integer,

~~~text
Norm((alpha)) = 3.
~~~

There are at most two integral ideals of norm 3.

If two positive solutions alpha_1, alpha_2 generate the same ideal, then

~~~text
alpha_2 = epsilon * alpha_1
~~~

for a totally positive norm-one unit epsilon.

For a nontrivial such epsilon>1,

~~~text
epsilon + epsilon^(-1)
~~~

is an integer at least 3.

Using

~~~text
conj(alpha) = -3/alpha

4*d*sqrt(T) = alpha + 3/alpha,
~~~

the proposed denominator ratio is

~~~text
d_2/d_1
=
(epsilon*x + epsilon^(-1))/(x+1),

x = alpha_1^2/3 > 1.
~~~

Hence

~~~text
d_2/d_1
>=
(epsilon + epsilon^(-1))/2
>=
3/2.
~~~

But fixed r and one dyadic shell imply

~~~text
sqrt(D/r) <= d < sqrt(2D/r),
~~~

so two denominators in the shell have ratio strictly below sqrt(2).

Since

~~~text
sqrt(2) < 3/2,
~~~

each norm-3 ideal orbit contributes at most one point; at most two ideals give
the fiber bound 2.

---

## A1 — attack every algebraic-number-theory step

Check carefully:

1. Is alpha always an algebraic integer in the full ring of integers O_K,
   including T == 1 mod 4?

2. Does the principal ideal (alpha) always have absolute ideal norm exactly 3?

3. Are there indeed at most two integral ideals of norm 3 in an arbitrary
   real quadratic field?

4. Does this remain true in the split, ramified, and inert cases at 3?

5. If two alpha generate the same ideal, is their quotient necessarily a unit
   of norm +1 rather than -1?

6. Is the quotient automatically totally positive from the sign pattern of
   alpha and its conjugate?

7. Is its trace epsilon + epsilon^(-1) necessarily an integer?

8. Can a nontrivial totally positive norm-one quadratic unit have trace 2 or
   otherwise violate the >=3 gap?

9. Is x=alpha_1^2/3 always >1 on the production witness range?

10. Is the ratio identity for d_2/d_1 exact?

11. Is the inequality

~~~text
d_2/d_1 >= (epsilon + epsilon^(-1))/2
~~~

valid in the required ordering?

12. Does the dyadic shell genuinely force d_2/d_1 < sqrt(2) after fixing r?

13. Are there sign/order issues allowing two positive witnesses from the same
    unit orbit to evade the ratio argument?

14. Does the argument accidentally count generators rather than witnesses in
    a way that can duplicate a?

15. Is the T=1 edge genuinely harmless?

Do not merely say the proof is standard.

Either prove/reconstruct every step or identify the first real gap.

---

## A2 — search for counterexamples

Try hard to falsify the fiber bound.

Use exact arithmetic or a fresh numerical script if helpful.

Search beyond the SOL-000 range if computationally cheap.

Target:

~~~text
same T
same r
same dyadic D-shell
at least 3 witnesses.
~~~

Also search specifically for a fiber of size 2.

The existing scan found maximum 1 through a<=10^6, but this is not proof.

If a size-2 example exists, it is valuable because it validates the natural
constant 2.

If no example appears, do not silently strengthen the theorem to 1.

---

## A3 — determine the weakest correct theorem

Possible outcomes include:

~~~text
fiber <= 2 exactly as stated;

fiber <= C for another absolute C;

fiber <= 2 only after an extra primitive/sign hypothesis already present in
production;

fiber <= 2 fails but a nearby orbit-count statement survives.
~~~

State the weakest theorem that is actually justified.

Do not optimize the constant unless it matters to the exponent.

---

# Review target B — represented (r,S) sparsity

Even if target A succeeds, SOL-000 obtains only

~~~text
N_X(D)
<<
X^2 * D^(-2/3).
~~~

Combined with the generic squarefull bound, this improves the shell moment
from

~~~text
X^(7/4)
~~~

to

~~~text
X^(3/2),
~~~

still superlinear.

Therefore the next genuine issue is not the fixed-fiber constant.

It is the number of represented parameter pairs.

Production and SOL-000 give the box:

~~~text
r^3 < 2D

D*S <= 3*(X+1)^2

r squarefree

S squarefree

Coprime r S

T=r*S squarefree

all prime divisors of r are 1 mod 3.
~~~

A pair contributes only if the primitive conic/norm equation has a production
witness:

~~~text
y^2 + 3 = 4*r*S*d^2

r divides d

Coprime y d

gcd(y,r*S) divides 3.
~~~

SOL-000 estimates all pairs in the box and loses the decisive power.

---

## B1 — find the missing power-saving mechanism

Investigate whether represented pairs (r,S) are power-sparse inside the box.

Priority mechanisms:

### B1a — principal norm-3 ideal condition

Existence of a solution implies a norm-3 ideal in Q(sqrt(rS)) is principal.

Can this principal-splitting condition be counted strongly enough on average
over squarefree T=rS?

Do not assume class-group randomness without a theorem.

### B1b — large square divisors of the quadratic polynomial

Since

~~~text
F(a) = T*d^2
~~~

with d large in large shells, reinterpret the problem as counting values of

~~~text
a^2+3a+3
~~~

with a large square divisor and controlled squarefree kernel.

Compare with known unconditional results on:

~~~text
large square divisors of quadratic polynomials,
squarefull values of quadratics,
squarefree-kernel distribution,
determinant method / square sieve / divisor switching.
~~~

If using literature, verify exact hypotheses and exponents.

Do not use ABC-conditional results.

### B1c — Eisenstein factorization

The discriminant -3 suggests factorization in Eisenstein integers.

Investigate whether

~~~text
y^2 + 3
~~~

or the original cubic GN structure admits a factorization that converts
represented (r,S) pairs into a divisor/incidence problem with stronger
coprimality than the real-quadratic formulation exposes.

Be alert to the fact that the real quadratic field changes with T, whereas
Z[omega] is fixed.

This may be the most promising route to a global average theorem.

### B1d — average Pell orbit incidence

Instead of worst-case fixed T, count solutions averaged over T in the allowed
height region

~~~text
D^2*T^3 < 54*(X+1)^6.
~~~

Can standard bounds for integral points on the family

~~~text
y^2 - 4*T*d^2 = -3
~~~

produce a power saving after averaging T?

Do not count every T and multiply by an O(1) fiber if a stronger family-level
estimate exists.

### B1e — r divides d

The production condition r|d is stronger than a generic Pell equation.

Write d=r*u, so

~~~text
y^2 + 3 = 4*S*r^3*u^2.
~~~

Investigate whether this cubic occurrence of r creates a useful determinant,
sieve, or factorization constraint.

This condition is already responsible for M=u^2*r^3; look for a second use
that genuinely reduces represented pairs.

---

## B2 — quantitative threshold

Any proposed sparsity theorem must be propagated to the capstone exponent.

SOL-000's box count is

~~~text
X^2 * D^(-2/3).
~~~

To approach the earlier near-linear target, an additional saving of rough size

~~~text
X / D^(1/6)
~~~

is needed over that box count.

Do not call a mechanism sufficient unless you compute its actual X,D
exponents.

For every serious candidate state:

~~~text
representedPairCount(X,D)
<=
explicit X,D bound
~~~

and then derive the corresponding shell moment exponent after multiplying by

~~~text
D^(3/8).
~~~

---

# Review of the new scratch theorem

SOL-000 has one new kernel-checked scratch result:

~~~text
D^2*T^3 < 54*(X+1)^6.
~~~

The proof combines:

~~~text
D*S <= 3*(X+1)^2

r^3 < 2D

T=r*S.
~~~

Audit this derivation independently.

If correct, classify it as:

~~~text
SCRATCH-PROVED / mathematically valid
~~~

but do not treat it as production until a later implementation gate.

Also decide whether a sharper constant or exponent is possible from existing
production facts.

Only pursue sharpening if it changes later counting.

---

# Mandatory regression audit

Any theorem you endorse must survive:

~~~text
M=169 collisions;

M=8281 four-witness collision;

the infinite complement-3 Pell family;

independent paired exact depths;

arbitrarily large coprime paired repeated parts;

arbitrary finite Hensel lifting;

all three mod-49 seven states.
~~~

Explain why the endorsed theorem does not contradict each regression.

---

# External research

Use web/literature aggressively if it helps review target B.

Priority topics:

~~~text
norm -3 equations in real quadratic fields

principal prime ideals above 3

large square divisors of quadratic polynomials

squarefull values of quadratic polynomials

squarefree kernels of quadratic values

average Pell equations

integral points on quadratic twists/conics

Eisenstein integer factorization

square sieve

determinant method

binary quadratic forms / class groups
~~~

For every external result:

~~~text
give exact statement/hypotheses;

state whether unconditional;

state the quantitative exponent;

state whether it is actually strong enough here.
~~~

Do not rely on vague literature analogies.

---

# No production implementation

During ASTRA-001:

~~~text
DO NOT create DkMath production modules.

DO NOT update DkMath/ABC.lean.

DO NOT create a provider or conjecture object.

DO NOT add an axiom.

DO NOT claim ABC.
~~~

Scratch Lean and numerical diagnostics are allowed.

---

# Required output

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-001.md
~~~

Title:

~~~text
# ASTRA-001 — norm-minus-three fiber and represented-pair review
~~~

The report must contain:

## 1. Fiber theorem verdict

One of:

~~~text
VALID

VALID WITH MODIFICATION

FALSE
~~~

with a complete mathematical reason.

## 2. Detailed gap audit

Address A1 items 1–15 explicitly.

## 3. Counterexample search

Report whether fiber size 2 or >=3 was found.

## 4. Weakest correct theorem

State the exact theorem Astra endorses.

## 5. Height inequality audit

Confirm or reject

~~~text
D^2*T^3 < 54*(X+1)^6.
~~~

## 6. Quantitative consequence

Re-derive the X^2 D^(-2/3) bound if justified and the X^(3/2) hybrid moment
exponent.

## 7. Represented-pair sparsity review

Analyze B1a–B1e and prune aggressively.

## 8. External theorem ledger

For any literature result used, record exact hypothesis and exponent.

## 9. Best next theorem

State the weakest new theorem that could plausibly supply the missing power
saving beyond the box count.

## 10. Production recommendation

Choose one:

~~~text
A. implement only the validated fixed-(T,r) fiber theorem now;

B. do not implement yet; first pursue the represented-pair theorem;

C. abandon this route.
~~~

Explain why.

## 11. Verdict

Use one of:

~~~text
Outcome A — validated route with next theorem isolated

Outcome B — fiber valid but global sparsity still unresolved

Outcome C — candidate route fails.
~~~

---

# Stop condition

Stop after report-001.md.

Do not create a production instruction automatically.

The report will be reviewed before any Lean production checkpoint is opened.
