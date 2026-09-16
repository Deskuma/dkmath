# instruction-011 — LUNA realized witness/incidence extraction

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-011**.

LUNA-010 made the remaining research target an exact dyadic shell count:

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D.
~~~

Do not estimate that count here.

Instead, expose exactly what the shell count is counting in terms of actual
canonical witnesses.

The target deterministic picture is:

~~~text
actual points a in [1,X]
        |
        | full repeated part M(a)
        v
realized large moduli
        |
        v
dyadic modulus shell [D,2D)
~~~

with exact image/fiber theorems.

This checkpoint should connect:

- witness points,
- full repeated moduli,
- dyadic shells,
- canonical complements,
- and the existing spacing theorem,

without adding any new global incidence estimate.

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
report-010.md
report-009.md
report-008.md
review-007.md
~~~

Then inspect:

~~~text
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessCubicIncidenceObstruction.lean
DkMath/ABC/GNExcessCubicRealizedDyadic.lean
DkMath/ABC/GNExcessCubicRealizedModuli.lean
~~~

Treat production source as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-011.md.

Report exact declarations, finite-set equalities, verification, and the
remaining research boundary.

---

# Part I — canonical full repeated-modulus map

Introduce a small named map if it improves readability.

Recommended:

~~~lean
def GNExcessCubicFullRepeatedModulus (a : ℕ) : ℕ :=
  GNNonExceptionalRepeatedPart 3 a 1
~~~

A nearby name is acceptable.

This is only an abbreviation-level semantic coordinate.

Do not create a new mathematical object unrelated to the existing repeated
part.

Provide simp/theorem API only if needed.

---

# Part II — realized-large witness space

Define the actual canonical points in the interval whose full repeated modulus
crosses the large boundary.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeWitnessSpace
    (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun a => X + 1 < GNExcessCubicFullRepeatedModulus a)
~~~

Using Icc 0 X with an explicit positivity filter is also acceptable.

Membership theorem:

~~~text
a ∈ witnessSpace X
<->
1 ≤ a
and a ≤ X
and X+1 < M(a).
~~~

Do not infer any cardinality estimate.

---

# Part III — exact image equals the realized modulus space

This is the first main theorem.

Prove:

~~~text
(witnessSpace X).image GNExcessCubicFullRepeatedModulus
=
GNExcessCubicRealizedLargeModulusSpace X.
~~~

Recommended theorem name:

~~~lean
GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace
~~~

Proof directions:

## witness -> modulus

Use the LUNA-009 safe membership bridge:

~~~lean
mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart
~~~

## modulus -> witness

Use the LUNA-006 / LUNA-008 realized modulus witness theorem or complement
packet to extract an actual positive point a with the exact repeated-part
equality.

This theorem is exact.

Do not claim the repeated-modulus map is injective on points.

The LUNA-008 collision regressions explicitly show it is not.

---

# Part IV — shell witness space

Define the actual points whose full repeated modulus lies in a chosen dyadic
shell.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeWitnessSpace X).filter
    (fun a =>
      D ≤ GNExcessCubicFullRepeatedModulus a ∧
      GNExcessCubicFullRepeatedModulus a < 2 * D)
~~~

Provide membership API.

Then prove the exact shell image theorem:

~~~text
(shellWitnessSpace X D).image GNExcessCubicFullRepeatedModulus
=
GNExcessCubicRealizedLargeModulusShell X D.
~~~

Recommended theorem name:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell
~~~

This should be an exact finite-set equality.

---

# Part V — shell count is bounded by witness count

Define, if useful:

~~~lean
def GNExcessCubicRealizedLargeModulusShellWitnessCount
    (X D : ℕ) : ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).card
~~~

Then prove the deterministic inequality:

~~~text
GNExcessCubicRealizedLargeModulusShellCount X D
<=
GNExcessCubicRealizedLargeModulusShellWitnessCount X D.
~~~

This is just card(image) <= card(source).

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellCount_le_witnessCount
~~~

Important:

This is **not** the needed shell-count estimate.

It merely makes the loss from point multiplicity explicit.

---

# Part VI — exact full-repeated witness fiber

For a fixed modulus M, define its actual canonical witness fiber inside [1,X].

Recommended:

~~~lean
noncomputable def GNExcessCubicFullRepeatedWitnessFiber
    (X M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun a => GNExcessCubicFullRepeatedModulus a = M)
~~~

Provide:

~~~text
a ∈ fiber X M
<->
1 ≤ a
and a ≤ X
and M(a)=M.
~~~

For a modulus in the realized large modulus space, prove the fiber is nonempty.

Recommended:

~~~lean
GNExcessCubicFullRepeatedWitnessFiber_nonempty_of_mem_modulusSpace
~~~

Do not prove or assume a uniform cardinality bound.

---

# Part VII — shell witness space partitions by modulus fibers

For a shell modulus M, every witness in its full-repeated fiber belongs to the
shell witness space.

Prove an exact partition theorem in whichever finite-set form is easiest.

Conceptually:

~~~text
shellWitnessSpace X D
=
biUnion M in modulusShell X D,
  fullRepeatedWitnessFiber X M.
~~~

Because distinct M give disjoint equality fibers, this should be an exact
partition.

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_fibers
~~~

Also prove pairwise disjointness of the fibers, or use it directly in the card
identity.

Then prove:

~~~text
shellWitnessCount X D
=
sum M in modulusShell X D,
  (fullRepeatedWitnessFiber X M).card.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards
~~~

This is valuable because it separates:

~~~text
number of distinct moduli
~~~

from:

~~~text
multiplicity of point witnesses per modulus.
~~~

No bound is asserted.

---

# Part VIII — complement packet from shell-witness membership

For every:

~~~text
a ∈ shellWitnessSpace X D,
~~~

expose the canonical complement facts directly.

Preferred theorem shape:

~~~text
let M := GNExcessCubicFullRepeatedModulus a
let S := GNExcessCubicComplement a

1 ≤ a
a ≤ X
D ≤ M
M < 2D
X+1 < M
M*S = a^2 + 3*a + 3
Squarefree S
Coprime M S
S ≤ X
~~~

The exact theorem may return a conjunction or a small packet.

Recommended name:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitness_complement_packet
~~~

Reuse LUNA-008 theorems.

Do not redo factorization arguments.

This theorem lets future research use the shell coordinate and complement
coordinate simultaneously.

---

# Part IX — fixed-modulus spacing inside a witness fiber

Use the production theorem:

~~~lean
cubicQuadratic_commonDivisor_le_spacingProduct
~~~

to prove the direct full-repeated-fiber version.

For:

~~~text
a < b
a,b ∈ fullRepeatedWitnessFiber X M
~~~

prove:

~~~text
M ≤ (b-a)*(a+b+3).
~~~

Recommended theorem:

~~~lean
GNExcessCubicFullRepeatedWitnessFiber_spacing
~~~

Then derive the interval-uniform form:

~~~text
M ≤ (b-a)*(2*X+3).
~~~

Recommended theorem:

~~~lean
GNExcessCubicFullRepeatedWitnessFiber_spacing_le_interval
~~~

or an orientation reflecting the inequality.

This is deterministic and already implicit in LUNA-008.

Do not convert it into a global fiber-card bound unless the proof is completely
routine and introduces no new combinatorial machinery.

---

# Part X — optional gap corollary

Only if short and clean, prove a parameterized consequence:

~~~text
K * (2*X+3) < M
a < b
a,b in fiber X M

=>

K < b-a.
~~~

This gives a usable lower gap without floor/ceiling definitions.

Recommended theorem:

~~~lean
GNExcessCubicFullRepeatedWitnessFiber_gap_gt_of_mul_lt_modulus
~~~

This is optional.

Do not introduce Nat.ceil or a custom division framework merely for this
checkpoint.

---

# Part XI — exact image/card consequences for the whole realized space

If cheap, also prove:

~~~text
card realizedModulusSpace X
<=
card realizedLargeWitnessSpace X.
~~~

This follows from Part III.

It is useful as a global sanity theorem but is not the research estimate.

Do not combine it with the trivial bound witnessCount <= X and present that as
progress toward ABC.

---

# Part XII — negative theorem boundary

Document explicitly:

~~~text
The point-to-modulus map is not injective.

A shell may contain fewer distinct moduli than witness points because one
modulus can have several full-repeated witnesses.

The exact fibers introduced here are intended to expose that multiplicity, not
to assume it away.
~~~

Reference the existing regression module in a docstring if useful.

Do not duplicate the 169 / 8281 factorization certificates.

---

# What LUNA-011 is NOT

Do not attempt:

- a nontrivial upper bound for shellCount,
- a nontrivial upper bound for shellWitnessCount,
- a uniform upper bound for fiber.card,
- the ASTRA dyadic incidence estimate,
- paired relative-height exclusion,
- an ABC receiver theorem,
- quality coupling,
- any use of abc_main_axiom.

Do not package any unproved count estimate into a provider, structure, or
hypothesis class.

The output is exact incidence **coordinates**, not incidence **sparsity**.

---

## Suggested module layout

Preferred new module:

~~~text
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
~~~

It should import:

~~~text
GNExcessCubicRealizedDyadic
~~~

and contain:

- full repeated-modulus map,
- realized witness space,
- shell witness space,
- exact image theorems,
- full repeated witness fibers,
- fiber partition/card identity,
- complement packet,
- spacing consumers.

Avoid changes to older modules unless a tiny helper clearly belongs there.

Import the new module from DkMath.ABC immediately after
GNExcessCubicRealizedDyadic.

---

## Verification

At minimum run:

~~~bash
lake build DkMath.ABC.GNExcessCubicRealizedIncidence
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

- witness-space image = modulus-space,
- shell-witness image = shell,
- shell witness count = sum fiber cards,
- complement packet,
- spacing theorem.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-011.md
~~~

Title:

~~~text
# LUNA-011 — realized witness/incidence extraction
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. full repeated-modulus map,
3. realized-large witness space,
4. exact witness-image = modulus-space theorem,
5. shell witness space,
6. exact shell-witness image theorem,
7. shell count <= witness count,
8. full repeated witness fiber,
9. shell witness partition by fibers,
10. exact witness-count = sum fiber-card identity,
11. complement packet,
12. spacing / optional gap theorem,
13. whole-space cardinal consequence,
14. focused build,
15. ABC aggregator build,
16. no-placeholder / no-new-axiom result,
17. axiom audit,
18. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the current shell count has a completely explicit witness/fiber
interpretation:

~~~text
modulusShell(X,D)
=
image of actual shell witnesses under fullRepeatedModulus

shellWitnessCount(X,D)
=
sum over distinct shell moduli M
  card(fullRepeatedWitnessFiber X M).
~~~

and every shell witness carries the production certificate:

~~~text
F(a)=M*S
M in [D,2D)
M>X
S<=X
Squarefree S
Coprime M S.
~~~

Do not estimate any of these cardinalities.

After LUNA-011 the remaining research question should be stated exactly as:

~~~text
How can the arithmetic of F(a)=M*S and the spacing of each exact M-fiber
force a nontrivial upper bound on the number of distinct M in one dyadic
shell?
~~~

That is research.

LUNA-011 only makes the incidence geometry exact.
