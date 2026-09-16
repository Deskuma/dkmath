# review-007 — ASTRA realized cubic modulus reconnaissance review

## Verdict

ASTRA-007 did **not** reach Success A, B, or C from instruction-007.

There is no proved linear bound for

~~~text
sum M in GNExcessCubicRealizedLargeModulusSpace X, M^(3/8),
~~~

no reduction to an already controlled summable object, and no alternate
closure of the actual realized large contribution.

Nevertheless, the pass is mathematically valuable and should be retained as a
successful **research-narrowing checkpoint**.

Recommended classification:

~~~text
ASTRA-007
  OUTCOME: RESEARCH PARTIAL — HIGH-VALUE STRUCTURAL / FALSIFICATION PASS

aggregate closure:
  OPEN

new exact structure:
  STRONG

false shortcuts eliminated:
  MULTIPLE

Lean scratch preservation:
  SUCCESS

recommended next mode:
  Sol / Ultra reasoning, then Luna productionization
~~~

The important outcome is that the remaining obstruction is substantially more
specific than it was at LUNA-006.

---

## 1. Trust / evidence levels

This review distinguishes four levels.

### Lean production proved before ASTRA-007

The current production frontier from LUNA-006 remains:

~~~text
actual cubic 3/8 moment
<=
2*(X+1)*finiteEuler
+
sum M in GNExcessCubicRealizedLargeModulusSpace X, M^(3/8).
~~~

Every realized modulus already satisfies the production certificates:

~~~text
X + 1 < M <= 3*(X+1)^2

exists 1 <= a <= X,
  M = GNNonExceptionalRepeatedPart 3 a 1
  and
  M divides a^2 + 3*a + 3

prime q divides M
  -> q^2 divides M
  and q % 3 = 1.
~~~

ASTRA-007 does not change these production facts.

### Lean scratch proved during ASTRA-007

The persistent scratch-007.lean.txt contains compiled proofs for the new
structural lemmas reviewed below.

These are **not yet production declarations**.

### Numerically falsified / observed

numeric-007.py and validation-007.txt contain exact-integer searches and
regressions. These are useful for falsification and branch selection but are
not promoted to theorems.

### Open

All aggregate counting / incidence claims remain open unless explicitly marked
otherwise below.

---

## 2. Strongest new exact structure: the canonical repeated/complement split

The most important positive result of ASTRA-007 is the exact decomposition of

~~~text
F(a) := a^2 + 3*a + 3 = GN 3 a 1.
~~~

### 2.1 The exceptional prime 3 never contributes repeated depth

Scratch theorem:

~~~lean
not_nine (a : Nat) :
  not 9 divides a^2 + 3*a + 3
~~~

This is proved by the nine residue classes modulo 9.

Consequently, although the non-exceptional construction removes the exponent
prime 3, it removes no repeated prime-power contribution in this canonical
cubic family.

### 2.2 Non-exceptional repeated part equals the full repeated part

Scratch theorem:

~~~lean
full_repeated (a : Nat) :
  GNNonExceptionalRepeatedPart 3 a 1 =
    repeatedPrimePowerPart (GN 3 a 1)
~~~

This is a significant simplification.

For the canonical cubic b = 1 problem the frontier modulus is not merely a
selected non-exceptional divisor: it is the **complete prime-power part
containing every exponent at least two**.

### 2.3 General repeated/complement decomposition

For every nonzero natural n, scratch proves:

~~~text
n = repeatedPrimePowerPart(n) * S
S squarefree
gcd(repeatedPrimePowerPart(n), S) = 1,
~~~

where

~~~text
S = n / repeatedPrimePowerPart(n).
~~~

The compiled theorem is complement_decomposition and canonical_decomposition
specializes it to F(a).

Thus every canonical point has an exact decomposition

~~~text
F(a) = M(a) * S(a)

M(a) = GNNonExceptionalRepeatedPart 3 a 1
S(a) = F(a) / M(a)

Squarefree S(a)
Coprime M(a) S(a).
~~~

This is the preferred arithmetic coordinate system discovered in ASTRA-007.

### 2.4 Important terminology warning

S(a) is **not** the parity squarefree kernel of F(a).

Example:

~~~text
F(17) = 7^3
M(17) = 7^3
S(17) = 1.
~~~

A parity-kernel decomposition would retain a factor 7.

Any Pell / squareful parametrization must keep this distinction explicit.

---

## 3. Large realized modulus forces a genuinely small complement

Scratch first proved S <= X+1 and then sharpened it.

Compiled theorem complement_sharp gives, under

~~~text
0 < X
a <= X
M*S = a^2 + 3*a + 3
X+1 < M,
~~~

the exact bound

~~~text
S <= X.
~~~

Hence every realized large modulus admits the stronger certificate

~~~text
F(a) = M*S
X+1 < M
S <= X
Squarefree S
Coprime M S.
~~~

This is strictly stronger information than the LUNA-006 statement M divides
F(a).

It should be productionized before any future global counting proof is
attempted.

---

## 4. Closed route: point-to-modulus injectivity / at-most-two witnesses

This route is definitively false.

### 4.1 First small collision

The exact sieve found:

~~~text
M = 169 = 13^2

a = 21:
  F(a) = 3 * 169

a = 145:
  F(a) = 127 * 169.
~~~

Both have the same full repeated part 169.

The corresponding exact repeated-part evaluations were later added to the Lean
scratch.

### 4.2 Four-root full repeated-part collision

A stronger counterexample is:

~~~text
M = 8281 = 7^2 * 13^2

a = 2173
a = 3018
a = 5260
a = 6105.
~~~

All four points have **the same full repeated part** 8281.

The complements are different and squarefree:

~~~text
571
1101
3343
4503.
~~~

This kills all of the following shortcuts:

~~~text
point -> modulus injective

one modulus has at most two interval witnesses

full repeated-part equality removes mixed CRT roots

M > interval length implies at most one/two actual witness.
~~~

The distinction from LUNA-006 must be preserved:

~~~text
profile -> modulus
~~~

is production-proved injective, but

~~~text
point -> profile/modulus
~~~

need not be.

Status:

~~~text
CLOSED
~~~

---

## 5. Exact spacing theorem survives the collision counterexamples

Although witness uniqueness fails, the following scratch theorem compiles.

For a < b with

~~~text
M divides F(a)
M divides F(b),
~~~

one has

~~~text
M <= (b-a)*(a+b+3).
~~~

The Lean path is roots_difference followed by spacing, using

~~~text
F(b)-F(a) = (b-a)(a+b+3).
~~~

This gives a real spacing pressure.

For witnesses inside [0,X], a derived consequence is qualitatively

~~~text
b-a is at least on the scale M/(2X+3).
~~~

This is strongest for top-height moduli M on the scale X^2.

However, this is an **upper bound on witness multiplicity for one fixed
modulus**. It does not itself bound the number of distinct realized moduli,
so it does not close the current modulus moment.

Status:

~~~text
PROVED-IN-SCRATCH
useful local incidence input
not an aggregate closure
~~~

---

## 6. Closed shortcut: bounded / injective complement coordinate

The small complement is structurally useful, but it is not a unique or
bounded-multiplicity label.

Numerics found repeated complements, including:

~~~text
S = 3:
a = 21, 312, 4365, 60816, ...

S = 1:
a = 17, 88915, ...
~~~

ASTRA then upgraded the S=3 phenomenon from numerics to a compiled infinite
family.

### 6.1 Pell-type recurrence

Scratch defines

~~~text
(a,d)
  -> (7a + 12d + 9,
      4a + 7d + 6)
~~~

and proves:

~~~text
pell_invariant
pell_repeated
pell_strictMono
pell_complement
~~~

Starting from (0,1), the a coordinates include

~~~text
0, 21, 312, 4365, 60816, ...
~~~

and satisfy exactly

~~~text
F(a) = 3*d^2
M(a) = d^2
S(a) = 3.
~~~

Therefore a **fixed bounded complement** can occur at arbitrarily many points
as the interval expands.

This rules out:

~~~text
uniform O(1) multiplicity for a fixed complement S

complement injectivity

small S alone implies only finitely/boundedly many witnesses.
~~~

It does not show unbounded multiplicity for one fixed modulus; the modulus
changes along the Pell family.

Status:

~~~text
CLOSED as a naive complement-count shortcut
OPEN as a Pell/conic counting route
~~~

---

## 7. Norm / discriminant geometry: useful exact identities, no counting theorem

Several algebraic identities compile.

### 7.1 Discriminant form

~~~text
4*F(a) = (2a+3)^2 + 3.
~~~

Scratch theorem discriminant proves this.

The theorem no_square also proves F(a) is never an ordinary square because it
lies strictly between (a+1)^2 and (a+2)^2.

### 7.2 Pell shell

If a squareful modulus is parametrized in the standard form

~~~text
M = d^2*r
~~~

with squarefree parity factor r, then from

~~~text
F = M*S
~~~

one reaches a negative-Pell-type equation of the shape

~~~text
(2a+3)^2 - 4*(S*r)*d^2 = -3.
~~~

The report correctly notes that r is essential. Replacing the Pell parameter
by S alone is false at odd repeated exponents such as 7^3.

### 7.3 Eisenstein norm multiplication

Scratch theorem norm_square_product checks the exact ring identity behind

~~~text
N((s+t*w)(u+v*w)^2)
  =
N(s+t*w) * N(u+v*w)^2.
~~~

For the canonical orientation one additionally needs a coefficient condition
equivalent to an oriented coefficient being plus or minus one; the live report
records the target as B = -1.

This is an interesting arithmetic representation problem, but the scratch
identity alone does not prove:

- existence of the required oriented factorization for every realized point,
- uniqueness,
- or a uniform count as the squarefree parameter varies.

Status:

~~~text
OPEN
algebra validated
global counting lemma missing
~~~

---

## 8. Height-only squareful counting is too weak at the exponent level

ASTRA-007 performed an important exponent audit.

Ignoring the witness equation and counting all squareful integers in a dyadic
shell D <= M < 2D gives the elementary scale

~~~text
#squareful(M around D) = O(D^(1/2)).
~~~

At weight M^(3/8), this produces shell scale

~~~text
D^(1/2) * D^(3/8)
=
D^(7/8).
~~~

Since the cubic height reaches D on the scale X^2, the resulting top scale is

~~~text
X^(7/4),
~~~

far above the desired linear scale.

Therefore the following routes are closed:

~~~text
height bound + generic squareful counting

prime-shell restriction with no proved power saving

ordinary CRT root count with the boundary +1 left untouched.
~~~

This independently reconfirms the earlier Astra diagnosis:

> the remaining gain must be a **global arithmetic incidence gain**, not local
> Hensel uniqueness or generic squareful sparsity.

Status:

~~~text
CLOSED for elementary height-only counting
~~~

---

## 9. A precise sufficient shell-count target was identified

Let N_X(D) denote the number of **distinct realized moduli** in a dyadic shell
near D.

The live report identifies the sufficient research target

~~~text
N_X(D)
  <= C_epsilon * X^(1+epsilon) / sqrt(D)
~~~

for

~~~text
X+1 <= D less than or comparable to X^2
epsilon < 1/8.
~~~

Then the weighted shell contributes at most

~~~text
X^(1+epsilon) * D^(-1/8),
~~~

which is already linear-or-better at the lower large-boundary scale.

This is **not proved**.

It should be treated as a quantitative specification of the missing incidence
lemma, not as a provider assumption or a contract to insert into production.

The live report also records the broader exponent diagnostic:

~~~text
if the boundary shell error behaves like D^beta,
linear closure at the top scale requires beta <= 1/8.
~~~

This sharply tells future research how much power saving is actually needed.

---

## 10. Important underexplored signal: paired relative-large exclusion

The numerical script contains a potentially important signal that did not reach
a full ASTRA branch before resource exhaustion.

For each canonical point it also computed the repeated part of the swapped
quadratic

~~~text
G(a) = 3*a^2 + 3*a + 1.
~~~

Through the search range a <= 200000, the validation output records:

~~~text
BOTH ABOVE INTERVAL []
PAIR PRODUCT ABOVE INTERVAL SQUARED []
~~~

in the scan where the canonical repeated part M already satisfies

~~~text
M > a+1.
~~~

Thus no tested point had the swapped repeated part N also satisfy

~~~text
N > a+1.
~~~

This is **numerical only**.

It is nevertheless strategically important because it is not the false
statement already killed in ASTRA-001.

ASTRA-001 proved that:

~~~text
both orientations can have arbitrarily large repeated parts in absolute size.
~~~

The new numerical question is instead the relative-height statement:

~~~text
can both repeated parts simultaneously exceed the local boundary a+1?
~~~

Those are different claims.

The compiled scratch already contains two identities relevant to this route:

~~~text
paired_product
paired_complement_congruence
~~~

corresponding to

~~~text
F(a) * G(a) = 3*(a+1)^4 + a^2

3*F(a) - G(a) = 6*a + 8.
~~~

This relative paired-large question should be the **first new research branch**
examined after the ASTRA-007 material is productionized.

It may offer a more direct route than proving the full general shell incidence
bound.

Do not promote the numerical absence to a theorem without proof.

---

## 11. Branch status summary

### Branch A — repeated / squarefree complement

~~~text
structural decomposition:
  PROVED-IN-SCRATCH

S <= X:
  PROVED-IN-SCRATCH

aggregate summation:
  OPEN

complement injectivity / bounded multiplicity:
  FALSE
~~~

### Branch B — discriminant / Pell / Eisenstein norm

~~~text
algebra:
  PROVED-IN-SCRATCH

fixed-complement Pell family:
  PROVED-IN-SCRATCH

uniform varying-parameter count:
  OPEN
~~~

### Branch C — witness multiplicity

~~~text
point->modulus injectivity:
  FALSE

at-most-two:
  FALSE

spacing:
  PROVED-IN-SCRATCH

aggregate consequence:
  OPEN
~~~

### Branch D — generic squareful counting

~~~text
height-only route:
  CLOSED

required incidence exponent:
  IDENTIFIED

incidence theorem:
  OPEN
~~~

### Branch E — paired orientation after modulus extraction

~~~text
full investigation:
  NOT COMPLETED

relative-large exclusion:
  NUMERICALLY PROMISING

supporting identities:
  PROVED-IN-SCRATCH
~~~

---

## 12. Recommended Luna production work

Before another expensive deep-reasoning pass, the durable scratch results
should be promoted to production Lean.

Recommended next engineering checkpoint should include only stable facts, not
the unproved incidence target.

### High priority

1. not_nine
2. canonical equality of non-exceptional repeated part and full repeated part
3. generic repeated/complement decomposition
4. canonical squarefree / coprime complement API
5. realized-large complement bound S <= X
6. roots_difference
7. spacing

### Negative-regression protection

Preserve exact examples proving that the full repeated-part map on points is
not injective, especially:

~~~text
M=169 at a=21,145

M=8281 at four exact points.
~~~

These may be regression examples rather than public theorems.

### Optional research-support API

Productionizing the Pell family is useful if the next research route groups by
complement, because it permanently prevents a future false uniform
complement-multiplicity theorem.

It is not necessary for the main ABC facade.

---

## 13. Recommended next reasoning order

The next reasoning pass should **not** reopen broad five-branch autonomous
exploration.

Use one narrowly scoped branch per pass.

Recommended priority:

### Priority 1 — paired relative-height theorem

Investigate:

~~~text
M(a) > a+1
and
N(a) > a+1
~~~

for the two canonical cubic orientations.

First determine by exact algebra / Lean scratch whether simultaneous
relative-large behavior is impossible, or derive the sharpest product bound
available.

This is motivated by the current numerical scan but must be falsification-first
at much larger / constructed CRT examples.

### Priority 2 — complement / modulus incidence theorem

If paired relative-large fails, attack the precise shell-count problem N_X(D)
using the new exact decomposition

~~~text
F = M*S,
S <= X,
Squarefree S,
Coprime M S
~~~

plus the spacing / conic geometry.

### Priority 3 — Eisenstein coefficient-count route

Only pursue the norm-factorization route if it produces a uniform theorem over
varying squarefree parameters, not merely fixed-parameter Pell growth.

---

## 14. Operational review of the ASTRA run

The artifact-first protocol worked.

Despite the run exhausting its reasoning budget before producing a polished
final response, the useful work survived in:

~~~text
report-007.md
scratch-007.lean.txt
numeric-007.py
validation-007.txt
~~~

This validates the decision to require continuous serialization.

However, the observed consumption was too steep for a five-major-branch plan.

For future high-cost reasoning passes:

~~~text
one major mathematical branch per invocation
write findings immediately
compile scratch immediately
stop as soon as the branch is classified
use Luna for cleanup / productionization
~~~

is safer than asking one run to explore five branches.

The model cannot reliably observe the user's remaining quota, so quota reserve
must be managed externally rather than encoded as an internal percentage
target.

---

## 15. Final frontier after ASTRA-007

The current problem is no longer:

~~~text
deep Hensel lifts?
formal ghost profiles?
root-address charge?
profile coordinates?
generic squareful integers?
~~~

Those layers have either been eliminated or diagnosed.

The surviving arithmetic object is:

~~~text
F(a) = a^2 + 3*a + 3 = M(a)*S(a)

M(a):
  full repeated prime-power part
  X+1 < M(a) <= 3*(X+1)^2
  all prime support q == 1 mod 3

S(a):
  squarefree
  gcd(M(a),S(a)) = 1
  S(a) <= X
~~~

and the unresolved target remains

~~~text
sum distinct realized M(a)^(3/8).
~~~

The smallest useful missing theorem is not a local lifting statement.

It is a **global incidence theorem** connecting the quadratic witness a, the
full repeated part M, and the small squarefree complement S strongly enough to
save at least the required boundary exponent.

The numerically observed paired relative-large exclusion is currently the most
specific candidate for such a gain.

---

## Review decision

~~~text
ASTRA-007:
  ACCEPT AS RESEARCH CHECKPOINT

ABC:
  NOT PROVED

new aggregate bound:
  NOT PROVED

new structural arithmetic:
  YES — Lean scratch

major false routes closed:
  YES

next action:
  Luna productionize stable scratch
  then focused Sol/Ultra reasoning on paired relative height
~~~
