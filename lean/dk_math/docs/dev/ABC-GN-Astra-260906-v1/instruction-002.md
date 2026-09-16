# instruction-002 — LUNA production freeze of shell-fiber uniqueness

## Mission

This checkpoint is LUNA-002 for the v1 campaign.

The mathematical review in report-001.md and scratch-001.lean established a
new deterministic fact:

~~~text
for fixed Pell parameter T,
fixed cube-core r,
and one dyadic shell [D,2D),

there is at most one production witness.
~~~

It also established:

~~~text
inside one realized large modulus shell,

a |-> (r,S)

is injective,
~~~

where r is the oddPart of the full repeated modulus and S is the canonical
complement.

LUNA-002 must move only these elementary kernel-checked facts into production
DkMath.

Do not formalize any asymptotic estimate.
Do not formalize any external theorem.
Do not add new research mathematics.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v1

campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read first:

~~~text
report-001.md
scratch-001.lean
validation-001.txt

../ABC-GN-Astra-260906-v0/report-022.md
~~~

Inspect production source, especially:

~~~text
DkMath/ABC/GNExcessCubicPrimitivePell.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
DkMath/ABC/GNExcessCubicSquarefulPell.lean
~~~

Treat current production Lean as authoritative.

---

## Part I — production module

Preferred new module:

~~~text
DkMath/ABC/GNExcessCubicShellFiberUniqueness.lean
~~~

The purpose of the module is narrow:

~~~text
1. elementary separation of two norm-minus-three conic solutions;
2. uniqueness in one dyadic shell for fixed (T,r);
3. exact production shell-fiber card <= 1;
4. injectivity of the canonical (r,S) coordinate map inside one shell.
~~~

Do not put asymptotic shell-count estimates in this module.
Do not put Mordell-curve counting in this module.
Do not put external literature statements in this module.

---

## Part II — integer conic cross identity

Port the scratch theorem:

~~~text
conic_cross_identity
~~~

For integer solutions

~~~text
y1^2 + 3 = 4*T*d1^2
y2^2 + 3 = 4*T*d2^2
~~~

prove exactly:

~~~text
(y2*d1)^2 + 3*d1^2
=
(y1*d2)^2 + 3*d2^2.
~~~

Use the short algebraic proof from scratch-001.

This is a generic local lemma.

Do not mention quadratic fields in the proof.

---

## Part III — lower bound y >= 2d

Port the scratch theorem:

~~~text
conic_y_lower
~~~

Preferred shape:

~~~text
2 <= T
0 <= y
0 < d
y^2 + 3 = 4*T*d^2

=>

2*d <= y.
~~~

Use integers if that is the cleanest implementation.

Do not overgeneralize beyond what the separation proof needs.

---

## Part IV — denominator separation

Port the key scratch theorem:

~~~text
conic_no_close_denominators
~~~

Required conclusion:

for positive ordered denominators

~~~text
0 < d1 < d2
~~~

and two solutions of the same conic parameter T with T>=2,

~~~text
y1^2 + 3 = 4*T*d1^2
y2^2 + 3 = 4*T*d2^2,
~~~

prove:

~~~text
2*d1^2 <= d2^2.
~~~

Use the exact integer determinant argument already accepted in scratch-001:

~~~text
A = y2*d1
B = y1*d2

A^2 - B^2
=
3*(d2^2-d1^2)

A > B
A >= B+1
A^2-B^2 >= 2*B+1
B >= 2*d1*d2

therefore close denominators are impossible.
~~~

Keep the proof elementary.

No ideal/unit machinery.
No external theorem.

---

## Part V — production T >= 2 wrapper

Port or adapt:

~~~text
cubic_parameter_ge_two
~~~

For the production conic equation

~~~text
(2*a+3)^2 + 3
=
4*T*d^2,
~~~

prove

~~~text
2 <= T.
~~~

The scratch proof uses:

~~~text
T=0 -> contradiction

T=1 -> a^2+3a+3=d^2
       contradict cubicQuadratic_ne_square.
~~~

Reuse the existing production theorem cubicQuadratic_ne_square.

Do not reprove nonsquareness.

---

## Part VI — abstract dyadic shell uniqueness

Port:

~~~text
conic_shell_unique
~~~

Required theorem:

for natural numbers T,r,D,y1,y2,d1,d2,

~~~text
2 <= T

0 < d1
0 < d2

y1^2 + 3 = 4*T*d1^2
y2^2 + 3 = 4*T*d2^2

D <= r*d1^2 < 2D
D <= r*d2^2 < 2D
~~~

prove:

~~~text
y1 = y2
and
d1 = d2.
~~~

The proof should be a direct consumer of Part IV.

Handle both denominator orderings by trichotomy.

Do not add squarefreeness, coprimality, r|d, or witness-height assumptions.
They are unnecessary.

---

## Part VII — refined production shell fiber

Define the production finite set.

Preferred name:

~~~text
GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber
~~~

with arguments X D T r.

Conceptually:

~~~text
existing PellParameterFiber X D T

filtered by

oddPart (FullRepeatedModulus a) = r.
~~~

Provide an exact membership theorem.

Required RHS:

~~~text
a in existing PellParameterFiber X D T
and
oddPart (FullRepeatedModulus a) = r.
~~~

If a shorter name fits current local naming conventions better, use it and
document the choice in report-002.

---

## Part VIII — production fiber is subsingleton

Prove:

~~~text
any two members of the refined fiber are equal.
~~~

Recommended theorem name:

~~~text
GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_subsingleton
~~~

The proof should:

1. obtain existing production witness packets;
2. obtain the squareful coordinate M = r * evenPart(M)^2;
3. obtain the primitive conic equation y^2+3 = 4*T*d^2;
4. invoke conic_shell_unique;
5. use injectivity of a |-> 2*a+3.

Do not replicate arithmetic already available in production packets.

---

## Part IX — card <= 1

Main finite-set theorem:

~~~text
refinedFiber.card <= 1.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one
~~~

Preferred proof:

~~~text
Finset.card_le_one.mpr refinedFiber_subsingleton
~~~

The stronger bound one is the canonical production result.

Do not add a card <= 2 theorem unless an existing consumer genuinely needs it.

---

## Part X — shell canonical pair injectivity

Prove:

~~~text
Set.InjOn
  (fun a =>
    ( oddPart (GNExcessCubicFullRepeatedModulus a),
      GNExcessCubicComplement a ))
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D : Set Nat).
~~~

Recommended theorem name:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_pair_injective
~~~

This theorem is local to one shell.

It does NOT prove:

~~~text
a |-> M(a) injective

a |-> S(a) injective

global a |-> (r,S) injective across different shells.
~~~

The proof should reconstruct:

~~~text
r = oddPart M(a)

T = r * S(a)
~~~

for two witnesses with equal pairs, put them into the same refined fiber, and
use the subsingleton theorem.

It must remain compatible with the known collisions:

~~~text
M=169
M=8281
the complement-3 Pell family.
~~~

---

## Part XI — optional exact pair-space cardinality

Only if extremely cheap, define or reuse the image of shell witnesses under

~~~text
a |-> (r,S)
~~~

and derive:

~~~text
pairSpace.card
=
shellWitnessSpace.card.
~~~

This is optional.

Do not grow a new incidence hierarchy around it.

---

## Part XII — optional height inequality

SOL-000 also scratch-proved:

~~~text
D^2*T^3 < 54*(X+1)^6
~~~

for represented shell Pell parameters.

If it ports trivially from existing production inequalities, it may be
included.

If it causes engineering expansion, skip it.

Do not spend this checkpoint sharpening 54 to 27.

Priority:

~~~text
fiber uniqueness
pair injectivity
height inequality only if cheap.
~~~

---

## Part XIII — explicit negative boundaries

Document in the module/report:

~~~text
PROVED:

fixed (T,r) + one dyadic shell -> at most one witness.

inside one shell:
a |-> (r,S) is injective.

NOT PROVED:

a |-> M injective.

fixed S has bounded multiplicity globally.

fixed T has bounded multiplicity globally.

N_X(D) is near-linear.

balanced-box power saving.

Helfgott-Venkatesh specialization in Lean.

ABC.
~~~

This distinction is mandatory.

---

## Part XIV — do not productionize research analytics

Do NOT formalize in this checkpoint:

~~~text
N_X(D) << sqrt(D)

N_X(D) << X^(2/3)

moment O(X^(17/12))

Mordell integral-point counting

Helfgott-Venkatesh Corollary 3.11

Helfgott-Venkatesh Lemma 4.1

N_X(D) <<_epsilon X^(2+epsilon) D^(-4/5)

moment O_epsilon(X^(31/24+epsilon))

balanced-box Q(B)

Q(B) << B^(2-delta+epsilon)

Eisenstein factorization existence.
~~~

The scratch Mordell and Eisenstein identities remain research artifacts for
now.

---

## Part XV — public import

Import the new module from:

~~~text
DkMath/ABC.lean
~~~

Place it after the existing Pell/incidence chain in dependency order.

Do not reorder unrelated imports.

---

## Part XVI — report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-002.md
~~~

Title:

~~~text
# LUNA-002 — shell-fiber uniqueness production freeze
~~~

Report:

1. files changed;
2. conic cross identity;
3. conic y lower bound;
4. denominator separation;
5. production T>=2 wrapper;
6. abstract shell uniqueness;
7. refined production (T,r) fiber;
8. exact membership theorem;
9. subsingleton theorem;
10. card <= 1;
11. shell (r,S) injectivity;
12. optional pair-card result;
13. optional height inequality status;
14. compatibility with known modulus collisions;
15. focused build;
16. ABC aggregator build;
17. forbidden construct scan;
18. axiom audit;
19. exact remaining research frontier.

Do not include commit hashes.

---

## Part XVII — validation

At minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicShellFiberUniqueness
lake build DkMath.ABC
~~~

If a different final module name is chosen, use that name.

Scan changed production Lean for:

~~~text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
~~~

No new occurrences.

Audit principal theorem axioms:

~~~text
conic_no_close_denominators

conic_shell_unique

refined shell fiber card <= 1

shell pair injectivity.
~~~

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

No external theorem may enter the Lean dependency graph.

---

## Stop condition

Stop when production DkMath contains kernel-checked theorems equivalent to:

~~~text
fixed (T,r) and one dyadic shell
=>
at most one realized witness

and

inside one shell
a |-> (r,S)
is injective.
~~~

Do not start the balanced-box counting problem.

Do not formalize the 31/24 analytic bound.

Do not open LUNA-003 automatically.

After this checkpoint, remain in coding mode only for additional
already-validated deterministic facts selected explicitly by review.
