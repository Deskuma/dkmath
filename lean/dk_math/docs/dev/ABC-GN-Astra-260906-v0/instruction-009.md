# instruction-009 — LUNA Pell and incidence-obstruction fact freeze

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-009**.

LUNA-008 promoted the canonical repeated/complement coordinate

~~~text
F(a) = a^2 + 3*a + 3 = M(a) * S(a)
~~~

with:

~~~text
M(a) = full repeated prime-power part
S(a) squarefree
Coprime M(a) S(a)
realized-large => S(a) <= X.
~~~

ASTRA-007 also left two further categories of kernel-checked facts that should
now be made durable:

1. an explicit Pell-type infinite family with **constant complement 3**, and
2. a theorem recording the **necessary counting strength** forced by any
   linear bound on the realized modulus moment.

These are facts / obstruction theorems.  They are not a proof of the missing
global incidence estimate.

Do not resume open-ended research in this checkpoint.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read first:

~~~text
report-007.md
review-007.md
scratch-007.lean.txt
report-008.md
instruction-008.md
~~~

Then inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessCubicRealizedModuli.lean
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
~~~

Treat current production source as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-009.md.

Report mathematical declarations, verification, dependency boundaries, and the
remaining open frontier only.

---

# Part I — exact discriminant / nonsquare facts

Promote the stable ASTRA scratch identities if they are not already available
under equivalent production names.

## Discriminant identity

Target:

~~~text
4 * (a^2 + 3*a + 3)
=
(2*a + 3)^2 + 3.
~~~

Recommended name:

~~~lean
cubicQuadratic_discriminant_identity
~~~

This is elementary but useful for the Pell / norm interpretation.

## The canonical quadratic is never a square

Promote the scratch theorem:

~~~text
a^2 + 3*a + 3 != d^2.
~~~

Recommended name:

~~~lean
cubicQuadratic_ne_square
~~~

Use the elementary inequality:

~~~text
(a+1)^2 < a^2+3*a+3 < (a+2)^2.
~~~

Do not create general quadratic-polynomial machinery.

---

# Part II — repeated part of 3*d^2

The Pell family requires one small arithmetic bridge.

Promote the stable scratch theorem in production form:

~~~text
d != 0
3 does not divide d

=>

repeatedPrimePowerPart (3*d^2) = d^2.
~~~

Recommended theorem name:

~~~lean
repeatedPrimePowerPart_three_mul_sq
~~~

or a nearby repository-consistent name.

Then expose the canonical consumer:

~~~text
a^2 + 3*a + 3 = 3*d^2
d != 0
3 does not divide d

=>

GNNonExceptionalRepeatedPart 3 a 1 = d^2.
~~~

Recommended theorem name:

~~~lean
GNNonExceptionalRepeatedPart_three_one_eq_sq_of_quadratic_eq_three_sq
~~~

Use the LUNA-008 theorem:

~~~lean
GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart
~~~

rather than duplicating the exceptional-prime argument.

---

# Part III — freeze the Pell recurrence

Recommended new module:

~~~text
DkMath/ABC/GNExcessCubicComplementPell.lean
~~~

Define the exact recurrence from ASTRA-007.

A production-friendly shape is acceptable, for example:

~~~lean
def GNCubicComplementPell : Nat -> Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
      let (a, d) := GNCubicComplementPell n
      (7*a + 12*d + 9, 4*a + 7*d + 6)
~~~

A shorter repository-consistent name is also acceptable.

Prove the exact invariant for every n:

~~~text
a_n^2 + 3*a_n + 3 = 3*d_n^2
a_n % 3 = 0
d_n % 3 = 1.
~~~

Recommended theorem:

~~~lean
GNCubicComplementPell_invariant
~~~

Do not prove this merely for the first several examples; prove the induction
for all n.

---

# Part IV — exact repeated part and constant complement along the Pell family

Use Parts II–III and LUNA-008 to prove:

~~~text
GNNonExceptionalRepeatedPart 3 a_n 1 = d_n^2
~~~

and:

~~~text
GNExcessCubicComplement a_n = 3.
~~~

Recommended theorem names:

~~~lean
GNCubicComplementPell_repeatedPart
GNCubicComplementPell_complement_eq_three
~~~

Also prove strict growth of the witness coordinate:

~~~text
StrictMono (fun n => a_n).
~~~

Recommended theorem:

~~~lean
GNCubicComplementPell_strictMono
~~~

This gives a theorem-grade negative result:

> the same fixed complement S=3 occurs at arbitrarily large canonical
> witnesses.

If inexpensive, expose an explicit existence corollary:

~~~text
for every B,
exists a > B,
  GNExcessCubicComplement a = 3.
~~~

Recommended name:

~~~lean
exists_large_cubic_point_complement_eq_three
~~~

This corollary is preferred because it states the mathematical obstruction
directly without requiring consumers to know the recurrence internals.

Do not claim anything about the number of such points below X beyond what
strict monotonicity / existence actually proves.

---

# Part V — negative theorem boundary for complement multiplicity

The Pell family should be documented as a **counter-pressure theorem**, not as
an ABC-positive estimate.

A docstring should explicitly record:

~~~text
No theorem of the form

  "for every fixed small S, only O(1) canonical points have complement S"

can be justified merely from smallness of S.

In particular S=3 occurs at arbitrarily large witnesses.
~~~

Do not formulate an asymptotic counting theorem unless it follows immediately
from the explicit recurrence and is genuinely useful.

The primary purpose is future branch pruning.

---

# Part VI — membership bridge for a full repeated modulus

ASTRA scratch contained the stable helper:

~~~text
a in Icc 0 X
GNNonExceptionalRepeatedPart 3 a 1 = M
X+1 < M

=>

M in GNExcessCubicRealizedLargeModulusSpace X.
~~~

Promote this as a production theorem if no equivalent theorem already exists.

Recommended name:

~~~lean
mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart
~~~

This is a safe converse only for the **actual full repeated part at a point**.

Important boundary:

Do not generalize it to:

~~~text
arbitrary squareful divisor M of F(a)
  -> M is realized.
~~~

That converse is not available.

This helper is useful for the obstruction theorem below.

---

# Part VII — monotonicity / injectivity of the canonical quadratic

Promote the small ASTRA scratch fact:

~~~text
Function.Injective (fun a : Nat => a^2 + 3*a + 3).
~~~

Recommended theorem name:

~~~lean
cubicQuadratic_injective
~~~

A stronger StrictMono theorem is acceptable if it is equally easy:

~~~lean
StrictMono (fun a : Nat => a^2 + 3*a + 3)
~~~

and injectivity may then be a corollary.

Keep this elementary.

---

# Part VIII — squarefull block obstruction theorem

This is the second main deliverable.

ASTRA-007 produced a kernel-checked theorem showing a **necessary consequence**
of any eventual linear modulus-moment closure.

Consider a finite set A of points in a dyadic witness block:

~~~text
X <= a <= 2*X
~~~

such that the whole quadratic value is already its repeated part:

~~~text
GNNonExceptionalRepeatedPart 3 a 1
=
a^2 + 3*a + 3.
~~~

Promote the exact theorem:

~~~text
A.card * (X^2)^(3/8)
<=
sum M in GNExcessCubicRealizedLargeModulusSpace (2*X),
  M^(3/8).
~~~

Recommended theorem name:

~~~lean
cubicSquarefullBlock_card_mul_weight_le_realizedModulusMoment
~~~

or a nearby explicit name.

The theorem should retain the actual real-rpow expression used by the current
moment API.

Use:

- Part VI for membership of each full repeated value,
- Part VII for injectivity of the quadratic values,
- Finset image / subset sum,
- nonnegativity of Real.rpow.

Do not assume any unproved bound on the right-hand side.

---

# Part IX — optional conditional counting corollary

Only if it is a short, transparent consequence, expose the logical
interpretation of Part VIII.

For an arbitrary constant C, under a hypothesis such as

~~~text
realized modulus moment at 2X <= C * X
~~~

derive the corresponding upper bound on A.card in real-number form.

However:

- do not invent asymptotic notation,
- do not introduce a provider class,
- do not call this an incidence theorem,
- do not make an integer floor/ceiling conversion unless trivial.

It is acceptable to omit this corollary and leave Part VIII as the clean
necessary-condition theorem.

The important semantic message is:

~~~text
linear moment closure would force squarefull quadratic values in [X,2X]
to live on the X^(1/4) scale (up to constants).
~~~

The production theorem itself should remain exact and assumption-free.

---

# Part X — freeze exact paired identities only

ASTRA-007 compiled the elementary identities:

~~~text
F(a) = a^2 + 3*a + 3
G(a) = 3*a^2 + 3*a + 1

F(a) * G(a)
=
3*(a+1)^4 + a^2

3*F(a) - G(a)
=
6*a + 8.
~~~

These may be promoted if they fit cleanly in the new module or a small nearby
module.

Recommended names:

~~~lean
cubicOrientation_product_identity_one
cubicOrientation_linear_difference_one
~~~

Exact names are flexible.

These facts are useful for the next reasoning phase.

But do **not** add any theorem stating or assuming:

~~~text
both repeated parts cannot exceed a+1

M*N <= (a+1)^2

paired relative-large exclusion.
~~~

The current absence of such examples up to 200000 is numerical evidence only.

If the paired identities would clutter LUNA-009, defer them to LUNA-010.
The Pell and block-obstruction facts have priority.

---

# Part XI — research regressions

The LUNA-008 regression module already preserves:

~~~text
M=169 at two points
M=8281 at four points.
~~~

Do not duplicate these proofs.

Optionally add the first few Pell values as small regression examples in a
test module:

~~~text
(a,d) = (0,1)
(21,13)
(312,181)
(4365,2521)
~~~

and verify complement 3.

These are not required if the general recurrence theorem is already strong and
well tested.

Do not productionize the numerical 6-root / 12-root mixed-CRT observations in
this checkpoint unless exact Lean certificates already exist and are cheap.
They are not needed for the main API.

---

# What LUNA-009 is NOT

Do not attempt:

- the dyadic incidence estimate
  N_X(D) <= C_epsilon * X^(1+epsilon) / sqrt(D),
- a bound for the realized modulus moment,
- a bound for squarefull quadratic-value counts,
- paired relative-height exclusion,
- ABC quality coupling,
- descent,
- a new ABC-equivalent contract,
- any use of abc_main_axiom.

Do not turn a necessary condition into a sufficient theorem.

The squarefull-block theorem says:

~~~text
linear closure => strong squarefull-value sparsity is necessary
~~~

conceptually.

It does **not** prove that sparsity.

---

## Suggested module layout

Preferred:

~~~text
DkMath/ABC/GNExcessCubicComplementPell.lean
DkMath/ABC/GNExcessCubicIncidenceObstruction.lean
~~~

The first module contains:

- discriminant / nonsquare if not placed elsewhere,
- repeated part of 3*d^2,
- Pell recurrence,
- exact complement 3,
- strict growth / large-point corollary.

The second contains:

- full-repeated membership bridge,
- quadratic injectivity/monotonicity,
- squarefull block obstruction,
- optional paired identities.

If two modules create unnecessary boilerplate, one focused module is
acceptable.

Do not broadly refactor LUNA-008.

Import the new modules from DkMath.ABC in dependency order immediately after
GNExcessCubicComplement.

---

## Verification

At minimum run the focused builds for every new production module and:

~~~bash
lake build DkMath.ABC
~~~

If a new regression test is added, build it as well.

Scan changed Lean files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit axioms for the principal new theorems:

- repeatedPrimePowerPart_three_mul_sq,
- Pell invariant,
- Pell repeated part,
- Pell complement = 3,
- strict monotonicity / large-point corollary,
- full-repeated modulus-space membership bridge,
- squarefull block obstruction.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

---

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-009.md
~~~

Title:

~~~text
# LUNA-009 — Pell and incidence-obstruction fact freeze
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. declarations added,
3. discriminant/nonsquare facts,
4. repeated part of 3*d^2,
5. Pell recurrence definition,
6. invariant theorem,
7. exact repeated part and complement 3,
8. strict growth / arbitrarily large witness result,
9. full-repeated modulus membership bridge,
10. quadratic injectivity/monotonicity,
11. squarefull block obstruction theorem,
12. optional paired identities status,
13. regression status,
14. focused builds,
15. ABC aggregator build,
16. no-placeholder / no-new-axiom result,
17. axiom audit,
18. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the following ASTRA-007 facts are durable production theorems:

~~~text
1. There is an explicit infinite Pell-type family with

     GNExcessCubicComplement a_n = 3

   and a_n strictly increasing.

2. A dyadic block of points whose whole F(a) is repeated satisfies the exact
   lower-obstruction inequality

     card(A) * X^(3/4)
       <= realized modulus 3/8 moment at scale 2X.
~~~

Do not continue to prove the missing global incidence theorem.

After LUNA-009, the fact-freezing ledger should make two negative lessons
permanent:

~~~text
small complement does not imply bounded witness multiplicity;

any linear closure must encode a genuinely strong global sparsity phenomenon.
~~~

The next checkpoints may continue freezing stable exact identities before
returning to research reasoning.
