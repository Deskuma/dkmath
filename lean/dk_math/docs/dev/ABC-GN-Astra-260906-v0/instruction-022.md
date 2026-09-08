# instruction-022 — LUNA ABC–GN cubic research-frontier capstone

## Mission

This checkpoint is **LUNA-022** and is intended as a **fact-freezing pause point**.

The campaign has already productionized the deterministic chain from realized
profiles through:

~~~text
realized moduli
dyadic shells
witness/fiber incidence
complement coordinates
Pell/conic coordinates
exceptional 3 normalization
paired orientations
square-cube coordinates
mod-49 seven-depth states
finite seven-state incidence.
~~~

Do not add another local coordinate system.

Do not attempt new number theory.

Instead, compose the existing production theorems into one end-to-end frontier
theorem showing that the remaining mathematical input is an explicit bound on

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

ABC is not proved in this checkpoint.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read report-007 through report-021, with particular attention to:

~~~text
report-007.md
report-010.md
report-011.md
report-012.md
report-013.md
report-015.md
report-016.md
report-017.md
report-018.md
report-019.md
report-020.md
report-021.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
DkMath/ABC/GNExcessCubicRealizedDyadic.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicThreeSectorIncidence.lean
DkMath/ABC/GNExcessCubicSevenDepthIncidence.lean
~~~

Treat production Lean as authoritative.

Do not include branch HEAD hashes or commit hashes in report-022.md.

---

## Part I — capstone production module

Add:

~~~text
DkMath/ABC/GNExcessCubicResearchFrontier.lean
~~~

This module should contain theorem composition and concise status documentation
only.

It should not contain a new substantial arithmetic proof.

The module docstring must state clearly:

~~~text
PRODUCTION-PROVED:
  deterministic reduction through realized dyadic shell counts.

OPEN:
  a nontrivial upper bound for
  GNExcessCubicRealizedLargeModulusShellCount X D.

NOT CLAIMED:
  ABC, density, relative-height exclusion, or shell sparsity.
~~~

---

## Part II — end-to-end shell-card consumer

Compose the existing theorem

~~~text
exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment
~~~

with

~~~text
GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds.
~~~

Add the main capstone theorem.

Recommended name:

~~~text
exp_GNExcessMassAt_sum_cubic_three_eighths_le_of_dyadicShellCardBounds
~~~

Preferred logical shape:

~~~text
Given B : Nat -> Real,

if for every represented dyadic index k,

  shellCount X (2^k) <= B(k),

then

  sum over a in Icc 0 X of
    exp((3/8) * GNExcessMassAt ... a)

  <=

  2*(X+1)*finiteEuler

  +

  sum over represented dyadic k of
    B(k) * (2^(k+1))^(3/8).
~~~

Use the exact current names and casts.

This theorem should be a short composition of already proved results.

Do not enlarge the index set unless required by Lean engineering.

Do not introduce asymptotic notation.

---

## Part III — explicit frontier remains the existing shell count

Do not define a new conjecture object or provider.

The research object remains exactly:

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

Future research should prove an ordinary theorem bounding this quantity and
pass it explicitly into the capstone consumer.

Do not introduce:

~~~text
axiom cubicIncidenceBound
class HasCubicIncidenceBound
structure CubicIncidenceProvider
ABCIncidenceProvider
~~~

and do not create any equivalent global assumption wrapper.

---

## Part IV — document the exact dyadic support range

Record in the module docstring/report the existing endpoint theorem:

~~~text
k in actual realized dyadic index space
implies

X+1 < 2^(k+1)

and

2^k <= 3*(X+1)^2.
~~~

No logarithmic asymptotics.

No new theorem is required if the existing API is already discoverable.

---

## Part V — document the exact finite incidence ledger

Record the already-proved finite identities.

At minimum:

~~~text
shellCount <= shellWitnessCount

shellWitnessCount
=
sum of modulus-fiber cards

shellWitnessCount
=
sum of complement-fiber cards

shellWitnessCount
=
pairSpace.card

shellWitnessCount
=
sum of Pell-parameter-fiber cards.
~~~

Also record the sector refinements:

~~~text
fixed-T fiber
=
non-three sector + three sector

three-sector witnesses
=
sum over normalized T3 fibers

seven-sector shell
=
forward-deep + swap-deep + shallow-seven

repeated-product-seven witnesses
=
forward-deep + swap-deep.
~~~

These are documentation facts unless a tiny alias theorem materially improves
discoverability.

Do not create giant conjunction theorems just to mirror the report.

---

## Part VI — positive production ledger

In report-022.md, summarize the strongest positive production chain:

~~~text
1. realized large profile/fiber boundary transfer

2. exact cubic 3/8 realized modulus moment

3. exact distinct realized modulus space

4. exact dyadic shell partition

5. shell moment <= shellCount * shell upper weight

6. generic explicit B(k) shell-card consumer

7. witness/fiber incidence coordinates

8. complement and pair coordinates

9. squareful / Pell coordinates

10. exceptional-prime-3 normalization

11. finite 3-sector incidence

12. paired orientation factorization

13. paired square-cube coordinates

14. unique ordinary overlap prime 7

15. exact mod-49 three-state normalization

16. finite seven-state incidence

17. capstone end-to-end composition.
~~~

Do not state or imply that this proves ABC.

---

## Part VII — negative regression ledger

The report must collect the routes already ruled out.

### Ghost profiles

Raw profile space contains impossible compound profiles.

Repair:

~~~text
realized profile space
realized modulus space
exact realized dyadic shells.
~~~

### Point-to-modulus injectivity is false

Existing regression examples include repeated moduli 169 and 8281 at multiple
witnesses.

Do not duplicate their proofs.

### Small complement does not imply bounded witness multiplicity

Production Pell family gives complement 3 at arbitrarily large strictly
increasing witnesses.

### Local depth competition is false

Production paired-depth theorems allow independent arbitrarily deep exact
depths in opposite orientations.

### Coprime repeated parts do not imply smallness

Production theorem:

~~~text
exists_arbitrarily_large_coprime_cubic_repeated_parts.
~~~

### Hensel uniqueness is not global rarity

Simple roots lift arbitrarily deeply.

### Prime 7 normalization is not a density theorem

Production isolates:

~~~text
forward-deep residue 29 mod 49
swap-deep residue 22 mod 49
shallow-seven otherwise in the seven sector.
~~~

No state-count estimate follows merely from this classification.

---

## Part VIII — research target in documentation only

ASTRA-007 identified a sufficient target of rough shape:

~~~text
N_X(D)
<=
C_epsilon * X^(1+epsilon) / sqrt(D)
~~~

through the realized large range, with epsilon small enough.

Record this in report-022.md under an explicit heading:

~~~text
RESEARCH TARGET — NOT PROVED
~~~

Do not add this asymptotic form as a named production conjecture, axiom,
structure, or provider.

The Lean capstone should remain generic in B(k).

---

## Part IX — public import

Import:

~~~text
GNExcessCubicResearchFrontier
~~~

from DkMath.ABC after the current fact-freezing chain.

This module becomes the preferred research restart entry point.

Do not reorder unrelated imports.

---

## Part X — validation

Run at minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicResearchFrontier
lake build DkMath.ABC
~~~

Scan changed production Lean for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit the principal capstone composition theorem.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

Because this checkpoint should be mostly composition, any unexpected new trust
dependency is a red flag.

---

## Deliverables

Create:

~~~text
DkMath/ABC/GNExcessCubicResearchFrontier.lean

docs/dev/ABC-GN-Astra-260906-v0/report-022.md

docs/dev/ABC-GN-Astra-260906-v0/validation-022.txt
~~~

Title:

~~~text
# LUNA-022 — ABC–GN cubic research-frontier capstone
~~~

Update README / ROADMAP so that the capstone is immediately discoverable.

The report should include:

1. files changed,
2. capstone composition theorem,
3. exact shell-count research object,
4. dyadic support range,
5. positive production chain,
6. finite incidence ledger,
7. 3-sector status,
8. paired/7-sector status,
9. negative regression ledger,
10. research target marked NOT PROVED,
11. exact statements still open,
12. focused build,
13. ABC aggregator build,
14. forbidden-construct audit,
15. axiom audit,
16. recommendation to pause and reassess mathematics.

---

## Stop condition

Stop when one production theorem states:

~~~text
explicit finite shell-card bounds
=>
the current cubic 3/8 excess-sum bound.
~~~

There must be no hidden provider and no research axiom.

The report must state unmistakably:

~~~text
The deterministic Lean reduction is complete up to the finite arithmetic
quantity

  GNExcessCubicRealizedLargeModulusShellCount X D.

A genuinely new theorem bounding that quantity is still required.

ABC is not proved.
~~~

Do not continue into LUNA-023 automatically.

After LUNA-022 succeeds, stop and reassess the mathematics before adding more
production layers.
