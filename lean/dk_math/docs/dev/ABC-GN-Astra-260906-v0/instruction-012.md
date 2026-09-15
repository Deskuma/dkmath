# instruction-012 — LUNA complement-slice / incidence-pair coordinates

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-012**.

LUNA-011 exposed the exact witness and modulus-fiber meaning of the dyadic
shell count.  The next deterministic coordinate is the canonical complement

~~~text
S(a) = GNExcessCubicComplement a.
~~~

ASTRA-007 and LUNA-009 already show that neither coordinate alone is injective:

~~~text
a -> M(a)    is not injective;
a -> S(a)    is not injective.
~~~

However the pair

~~~text
a -> (M(a), S(a))
~~~

should be injective because production Lean already proves

~~~text
M(a) * S(a) = a^2 + 3*a + 3
~~~

and the canonical quadratic is injective.

LUNA-012 should freeze this exact two-coordinate incidence geometry.

Do **not** estimate any cardinality nontrivially.

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
report-011.md
report-010.md
report-009.md
report-008.md
~~~

Then inspect:

~~~text
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessCubicComplementPell.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
DkMath/ABC/GNExcessCubicRealizedDyadic.lean
~~~

Treat current production source as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-012.md.

Report exact definitions, bijective/image/partition facts, verification, and
the remaining research boundary.

---

# Part I — canonical incidence pair

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicComplementIncidence.lean
~~~

Define the canonical pair:

~~~lean
noncomputable def GNExcessCubicIncidencePair (a : ℕ) : ℕ × ℕ :=
  (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a)
~~~

The first coordinate is the full repeated modulus.
The second coordinate is the residual complement.

Provide projection lemmas if useful:

~~~text
(GNExcessCubicIncidencePair a).1 = M(a)
(GNExcessCubicIncidencePair a).2 = S(a).
~~~

Do not create a new independent modulus or complement definition.

---

# Part II — pair product recovers the canonical quadratic

Prove:

~~~text
pair(a).1 * pair(a).2
=
a^2 + 3*a + 3.
~~~

Recommended theorem:

~~~lean
GNExcessCubicIncidencePair_mul_eq_quadratic
~~~

This should be a short consumer of:

~~~lean
GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic
~~~

and the existing full-repeated-modulus abbreviation.

---

# Part III — global injectivity of the incidence pair

This is the first main theorem.

Prove:

~~~lean
theorem GNExcessCubicIncidencePair_injective :
    Function.Injective GNExcessCubicIncidencePair
~~~

Intended proof:

1. assume pair(a) = pair(b),
2. obtain equality of both coordinates,
3. multiply the equal coordinates,
4. use the pair-product theorem to derive

~~~text
a^2 + 3*a + 3 = b^2 + 3*b + 3,
~~~

5. conclude with production theorem:

~~~lean
cubicQuadratic_injective.
~~~

Important semantic result:

~~~text
M alone does not identify a;
S alone does not identify a;
the exact pair (M,S) does identify a.
~~~

This is a deterministic theorem, not an incidence sparsity estimate.

---

# Part IV — shell complement space

For one realized dyadic shell, define the finite set of complement values that
actually occur.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellComplementSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    GNExcessCubicComplement
~~~

Provide membership API:

~~~text
S ∈ shellComplementSpace X D
<->
exists a ∈ shellWitnessSpace X D,
  GNExcessCubicComplement a = S.
~~~

Do not claim complement injectivity.

---

# Part V — shell complement values are positive, small, squarefree

For:

~~~text
S ∈ shellComplementSpace X D,
~~~

prove:

~~~text
0 < S
S ≤ X
Squarefree S.
~~~

Recommended individual theorem names:

~~~lean
GNExcessCubicRealizedLargeModulusShellComplementSpace_pos
GNExcessCubicRealizedLargeModulusShellComplementSpace_le
GNExcessCubicRealizedLargeModulusShellComplementSpace_squarefree
~~~

or one compact packet theorem plus convenient projections.

Use the LUNA-011 shell-witness complement packet.

For positivity, derive it from the exact product:

~~~text
M*S = a^2+3*a+3 > 0
~~~

and positivity of M if needed.

A useful finite-set consequence is:

~~~text
shellComplementSpace X D ⊆ Finset.Icc 1 X.
~~~

Prove it if cheap.

This is exact support control, not a count estimate.

---

# Part VI — exact complement witness fiber

Define the complement equality fiber inside the shell witness space.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellComplementFiber
    (X D S : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => GNExcessCubicComplement a = S)
~~~

Membership theorem:

~~~text
a ∈ complementFiber X D S
<->
a ∈ shellWitnessSpace X D
and GNExcessCubicComplement a = S.
~~~

For every represented shell complement S, prove the fiber is nonempty.

Do not prove a uniform fiber-cardinality bound.

The Pell theorem from LUNA-009 is exactly why no such bound should be assumed
from smallness of S alone.

---

# Part VII — shell witnesses partition exactly by complement fibers

Prove pairwise disjointness of distinct complement fibers.

Then prove:

~~~text
(shellComplementSpace X D).biUnion
  (fun S => shellComplementFiber X D S)
=
shellWitnessSpace X D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_complementFibers
~~~

Equality orientation may be reversed.

Then prove the exact cardinal identity:

~~~text
shellWitnessCount X D
=
∑ S ∈ shellComplementSpace X D,
  (shellComplementFiber X D S).card.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_complementFiberCards
~~~

This is the complement-coordinate analogue of the LUNA-011 modulus-fiber
identity.

---

# Part VIII — shell incidence-pair space

Define the exact finite set of represented pairs:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellIncidencePairSpace
    (X D : ℕ) : Finset (ℕ × ℕ) :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    GNExcessCubicIncidencePair
~~~

Membership API:

~~~text
(M,S) ∈ pairSpace X D
<->
exists a ∈ shellWitnessSpace X D,
  incidencePair a = (M,S).
~~~

Because the pair map is injective, prove exact cardinal preservation:

~~~text
(pairSpace X D).card
=
shellWitnessCount X D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_card
~~~

This is a central exact theorem.

---

# Part IX — projections of the pair space

Prove the first-coordinate image is exactly the modulus shell:

~~~text
(pairSpace X D).image Prod.fst
=
GNExcessCubicRealizedLargeModulusShell X D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_fst_image_eq_shell
~~~

Prove the second-coordinate image is exactly the shell complement space:

~~~text
(pairSpace X D).image Prod.snd
=
GNExcessCubicRealizedLargeModulusShellComplementSpace X D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_snd_image_eq_complementSpace
~~~

These identities make the two many-to-one projections explicit.

Cheap cardinal consequences are allowed:

~~~text
shellCount X D ≤ pairSpace.card
shellComplementSpace.card ≤ pairSpace.card.
~~~

Do not present these trivial inequalities as sparsity progress.

---

# Part X — exact pair packet

For:

~~~text
(M,S) ∈ pairSpace X D,
~~~

prove existence of the unique witness and expose all stable arithmetic facts.

A preferred theorem shape is:

~~~text
exists a,
  a ∈ shellWitnessSpace X D
  and incidencePair a = (M,S)
  and
  1 ≤ a
  and a ≤ X
  and D ≤ M
  and M < 2D
  and X+1 < M
  and 0 < S
  and S ≤ X
  and Squarefree S
  and Nat.Coprime M S
  and M*S = a^2 + 3*a + 3.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePair_packet
~~~

If convenient, also prove uniqueness of the witness:

~~~text
∃! a, a ∈ shellWitnessSpace X D ∧ incidencePair a = (M,S).
~~~

This should follow immediately from pair injectivity.

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePair_existsUnique_witness
~~~

This uniqueness is safe.

It is **pair uniqueness**, not modulus uniqueness and not complement
uniqueness.

---

# Part XI — fixed-complement equation inside a complement fiber

For:

~~~text
a ∈ shellComplementFiber X D S,
~~~

prove the direct equation:

~~~text
GNExcessCubicFullRepeatedModulus a * S
=
a^2 + 3*a + 3.
~~~

and the shell bounds on the modulus:

~~~text
D ≤ GNExcessCubicFullRepeatedModulus a
GNExcessCubicFullRepeatedModulus a < 2D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellComplementFiber_equation
~~~

This is a convenience consumer for future fixed-S / Pell / conic arguments.

Do not solve or count the equation.

---

# Part XII — optional divisibility relation between two points of one complement fiber

Only if completely routine, for two points a,b with the same complement S,
derive the exact product relation:

~~~text
M(a)*S = F(a)
M(b)*S = F(b).
~~~

Do not attempt a new spacing theorem in S.

The LUNA-009 Pell family shows fixed S can recur indefinitely.

This part is optional and should not expand the checkpoint.

---

# Part XIII — exact two-way cardinal ledger

By the end of the checkpoint the following equalities should coexist:

~~~text
shellWitnessCount
=
∑ M in modulusShell, modulusFiber(M).card

shellWitnessCount
=
∑ S in complementSpace, complementFiber(S).card

shellWitnessCount
=
pairSpace.card.
~~~

Record these together in the module docstring or report.

This is the exact finite incidence ledger.

No nontrivial upper bound is asserted.

---

# Negative theorem boundaries

Do not infer:

~~~text
a -> M is injective
a -> S is injective

fixed M has O(1) witnesses
fixed S has O(1) witnesses

pairSpace.card is small

modulusShell.card is comparable to complementSpace.card.
~~~

Known production/regression facts explicitly warn against the first four kinds
of shortcuts.

The only injectivity requested here is:

~~~text
a -> (M(a),S(a)).
~~~

---

# What LUNA-012 is NOT

Do not attempt:

- a bound for shellCount,
- a bound for shellWitnessCount,
- a bound for either fiber cardinality,
- a bound for pairSpace.card,
- dyadic incidence sparsity,
- Pell/conic counting,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce a provider class or research assumption.

This checkpoint is exact coordinate geometry only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicRealizedIncidence
~~~

unless dependency order requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~bash
lake build DkMath.ABC.GNExcessCubicComplementIncidence
lake build DkMath.ABC
~~~

Scan changed Lean files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit axioms for:

- incidence-pair injectivity,
- complement-fiber partition,
- complement-fiber cardinal identity,
- pair-space cardinal preservation,
- pair-space projection equalities,
- unique pair witness.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-012.md
~~~

Title:

~~~text
# LUNA-012 — complement-slice / incidence-pair coordinates
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. canonical incidence pair definition,
3. pair-product theorem,
4. pair injectivity,
5. shell complement space,
6. positivity / squarefree / S≤X support facts,
7. complement fiber,
8. complement-fiber exact partition,
9. complement-fiber cardinal sum,
10. shell incidence-pair space,
11. exact pair-space cardinal preservation,
12. first/second projection image theorems,
13. exact pair packet / unique witness theorem,
14. fixed-complement equation consumer,
15. three-way cardinal ledger,
16. focused build,
17. ABC aggregator build,
18. no-placeholder / no-new-axiom result,
19. axiom audit,
20. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the shell incidence geometry is represented exactly in all three
coordinates:

~~~text
witness a

modulus M(a)

complement S(a)

pair (M(a),S(a)).
~~~

The key exact facts at stop are:

~~~text
a -> (M,S) is injective;

pairSpace.card = shellWitnessCount;

fst(pairSpace) = modulusShell;

snd(pairSpace) = complementSpace;

shellWitnessCount
  = sum modulus-fiber cards
  = sum complement-fiber cards.
~~~

Do not estimate any term.

After LUNA-012, the remaining research problem is a genuine finite lattice
incidence question:

~~~text
How sparse can the represented pairs (M,S) be forced to be, subject to

  M in [D,2D),
  X+1 < M,
  1 <= S <= X,
  Squarefree S,
  Coprime M S,
  M*S = a^2+3*a+3

for a unique canonical witness a?
~~~

That is research.

LUNA-012 only freezes the exact coordinate system.
