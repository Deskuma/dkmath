# instruction-014 — LUNA square-cube / Pell-parameter incidence ledger

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-014**.

LUNA-013 put every represented shell pair into the exact coordinates

~~~text
M = r*d^2

r = oddPart M
d = evenPart M
r divides d

T = r*S
Squarefree T

y^2 + 3 = 4*T*d^2.
~~~

The next deterministic step is to freeze two further coordinate layers that
are already implicit in those facts:

1. the canonical square-times-cube form

~~~text
M = u^2 * r^3,
~~~

and

2. the exact finite partition of shell witnesses by the squarefree Pell
parameter

~~~text
T = oddPart M * S.
~~~

No counting estimate is part of this checkpoint.

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
report-013.md
report-012.md
report-011.md
report-010.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicSquarefulPell.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
DkMath/ABC/SquareTailBasic.lean
~~~

Treat current production Lean as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-014.md.

Report exact definitions, finite-set identities, deterministic inequalities,
verification, and the remaining research boundary.

---

# Part I — canonical squareful quotient

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
~~~

Define the canonical quotient

~~~text
u(M) := evenPart M / oddPart M.
~~~

Recommended definition:

~~~lean
noncomputable def GNExcessCubicSquarefulQuotient (M : ℕ) : ℕ :=
  evenPart M / oddPart M
~~~

A shorter repository-consistent name is acceptable.

For nonzero squareful M, use

~~~text
oddPart M divides evenPart M
~~~

to prove the exact reconstruction

~~~text
evenPart M = oddPart M * GNExcessCubicSquarefulQuotient M.
~~~

Recommended theorem:

~~~text
evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient
~~~

Do not define an arbitrary quotient with an existential witness when the
canonical natural division coordinate is available.

---

# Part II — canonical square-times-cube identity

For nonzero squareful M prove the canonical identity

~~~text
M
=
(GNExcessCubicSquarefulQuotient M)^2
  * (oddPart M)^3.
~~~

Recommended theorem:

~~~text
squareful_eq_squareQuotient_sq_mul_oddPart_cube
~~~

This is the canonical version of the already proved existential theorem

~~~text
exists_sq_mul_cube_of_squarefull.
~~~

The proof should reuse:

~~~text
squareful_oddEven_packet
evenPart = oddPart * quotient.
~~~

Do not redo prime-factorization arithmetic.

If the multiplication orientation produced naturally is

~~~text
M = (oddPart M)^3 * quotient^2
~~~

also provide the preferred square-times-cube orientation by commutativity/ring
normalization.

---

# Part III — realized modulus square-cube packet

For

~~~text
M in GNExcessCubicRealizedLargeModulusSpace X,
~~~

prove a packet exposing

~~~text
0 < M
squarefull M

r = oddPart M
u = GNExcessCubicSquarefulQuotient M

Squarefree r
0 < r
0 < u

M = u^2 * r^3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusSpace_squareCube_packet
~~~

Exact conjunction order is flexible.

Positivity should be derived from the existing realized-modulus positivity and
the exact product identity.

Do not introduce roots or floor/cube-root functions.

---

# Part IV — cube-core bound inside one dyadic shell

For a represented shell pair or shell modulus prove the exact deterministic
bound

~~~text
(oddPart M)^3 <= M
~~~

and therefore

~~~text
(oddPart M)^3 < 2*D
~~~

for

~~~text
M in shell X D.
~~~

Recommended theorem names:

~~~text
oddPart_cube_le_of_squarefull
GNExcessCubicRealizedLargeModulusShell_oddPart_cube_lt
~~~

A proof via

~~~text
M = u^2*r^3
1 <= u
~~~

is preferred.

This is only a structural support bound.

Do not translate it into an asymptotic count of possible r.

---

# Part V — canonical Pell parameter map

Define the exact pair-level parameter

~~~text
T(M,S) := oddPart M * S.
~~~

Recommended definition:

~~~lean
noncomputable def GNExcessCubicPellParameter
    (p : ℕ × ℕ) : ℕ :=
  oddPart p.1 * p.2
~~~

or a two-argument definition if that is cleaner.

Keep the definition directly tied to the LUNA-012 incidence pair.

A witness-level abbreviation is optional.

---

# Part VI — shell Pell-parameter space

Define:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).image
    GNExcessCubicPellParameter
~~~

Provide the membership theorem:

~~~text
T in PellParameterSpace X D
<->
exists (M,S) in pairSpace X D,
  oddPart M * S = T.
~~~

Do not assert injectivity of the Pell-parameter map.

---

# Part VII — represented Pell parameters are positive and squarefree

For

~~~text
T in PellParameterSpace X D,
~~~

prove:

~~~text
0 < T
Squarefree T.
~~~

Recommended theorem names:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterSpace_pos
GNExcessCubicRealizedLargeModulusShellPellParameterSpace_squarefree
~~~

The squarefree theorem should directly consume the LUNA-013 pair theorem.

For positivity use the represented pair packet:

~~~text
oddPart M > 0
S > 0.
~~~

Do not add any count bound for the parameter space.

---

# Part VIII — deterministic cubic support bound for T

For represented T, expose the factorization data:

~~~text
T = r*S

r = oddPart M
r^3 < 2D
1 <= S <= X.
~~~

Recommended packet:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameter_packet
~~~

If clean, derive the exact natural inequality

~~~text
T^3 < (2*D) * X^3
~~~

for every represented T.

Reason:

~~~text
T^3 = r^3*S^3
r^3 < 2D
S^3 <= X^3.
~~~

This inequality is useful but optional if natural-number strict multiplication
creates disproportionate engineering work.

Do not introduce real cube roots.

---

# Part IX — Pell-parameter witness fiber

Define the actual shell witnesses sharing a fixed T.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiber
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a =>
      oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a = T)
~~~

Provide the exact membership theorem.

For every represented T, prove the fiber is nonempty.

Do **not** prove a uniform cardinality bound.

The Pell family already warns against naive fixed-parameter conclusions.

---

# Part X — exact partition by Pell-parameter fibers

Prove pairwise disjointness of distinct T-fibers.

Then prove the exact partition:

~~~text
(PellParameterSpace X D).biUnion
  (fun T => PellParameterFiber X D T)
=
shellWitnessSpace X D.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_pellParameterFibers
~~~

Then prove the exact cardinal identity:

~~~text
shellWitnessCount X D
=
sum T in PellParameterSpace X D,
  (PellParameterFiber X D T).card.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_pellParameterFiberCards
~~~

This adds the fourth exact incidence ledger coordinate after:

~~~text
modulus M
complement S
pair (M,S)
Pell parameter T.
~~~

No estimate is asserted.

---

# Part XI — exact conic equation inside a fixed-T fiber

For

~~~text
a in PellParameterFiber X D T,
~~~

prove existence of the canonical d:

~~~text
d = evenPart (GNExcessCubicFullRepeatedModulus a)
~~~

with

~~~text
(2*a+3)^2 + 3 = 4*T*d^2.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation
~~~

Also expose, if cheap:

~~~text
0 < d.
~~~

This should be a direct consumer of the LUNA-013 Pell identity.

Do not solve or count this conic.

---

# Part XII — pair-space partition by T

If clean, also define the pair-level T fiber:

~~~text
{ p in pairSpace | GNExcessCubicPellParameter p = T }.
~~~

Then prove its image under the unique-witness correspondence has the same
cardinality as the witness T-fiber.

This is optional.

The witness-level exact partition from Parts IX–X has priority.

---

# Part XIII — extended exact cardinal ledger

By the end of LUNA-014, the report should place together:

~~~text
shellWitnessCount
=
sum M in modulusShell, modulusFiber(M).card

shellWitnessCount
=
sum S in complementSpace, complementFiber(S).card

shellWitnessCount
=
pairSpace.card

shellWitnessCount
=
sum T in PellParameterSpace, PellParameterFiber(T).card.
~~~

This is an exact incidence ledger only.

Do not compare these terms nontrivially.

---

# Part XIV — regression boundary

Document explicitly:

~~~text
The Pell-parameter map is not assumed injective.

Fixed T is not assumed to have O(1) witnesses.

No sparsity follows merely from T being squarefree.
~~~

Do not create counterexample numerics unless already available in the campaign
records.

---

# What LUNA-014 is NOT

Do not attempt:

- counting Pell solutions,
- bounding PellParameterSpace.card,
- bounding PellParameterFiber.card,
- bounding shellCount,
- bounding shellWitnessCount,
- dyadic incidence sparsity,
- asymptotic squareful counting,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce provider classes or unproved hypotheses.

This checkpoint freezes exact coordinates only.

---

## Suggested module layout

Preferred new module:

~~~text
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
~~~

It should import:

~~~text
GNExcessCubicSquarefulPell
~~~

and contain:

- canonical squareful quotient,
- canonical square-times-cube identity,
- realized square-cube packet,
- cube-core shell bound,
- Pell-parameter definition,
- Pell-parameter space,
- Pell-parameter fibers,
- exact partition/card ledger,
- fixed-T conic equation.

Avoid modifying older modules unless a tiny generic helper clearly belongs
there.

Import the new module from DkMath.ABC immediately after
GNExcessCubicSquarefulPell.

---

## Verification

At minimum run:

~~~text
lake build DkMath.ABC.GNExcessCubicPellParameterIncidence
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

- canonical squareful quotient reconstruction,
- square-times-cube identity,
- realized square-cube packet,
- cube-core shell bound,
- represented T squarefree theorem,
- T-fiber partition,
- T-fiber cardinal identity,
- fixed-T conic equation.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-014.md
~~~

Title:

~~~text
# LUNA-014 — square-cube / Pell-parameter incidence ledger
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. canonical squareful quotient,
3. exact square-times-cube identity,
4. realized square-cube packet,
5. cube-core shell bound,
6. Pell-parameter map,
7. Pell-parameter space,
8. positivity/squarefree support,
9. optional T^3 support bound status,
10. Pell-parameter witness fiber,
11. exact T-fiber partition,
12. exact T-fiber cardinal sum,
13. fixed-T conic equation,
14. extended four-way cardinal ledger,
15. focused build,
16. ABC aggregator build,
17. no-placeholder / no-new-axiom result,
18. axiom audit,
19. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the existing conic coordinate has been expanded into the exact
square-cube and T-fiber ledger:

~~~text
M = u^2*r^3

r = oddPart M
u = evenPart M / oddPart M

T = r*S
Squarefree T

shellWitnessCount
=
sum T in PellParameterSpace,
  PellParameterFiber(T).card

and every witness in a fixed T fiber satisfies

  (2*a+3)^2 + 3 = 4*T*d^2.
~~~

Do not estimate any cardinality.

After LUNA-014, the same finite research frontier will be readable through
four exact coordinates:

~~~text
M-shell
S-slice
(M,S)-pair lattice
T-fixed negative-Pell conic.
~~~

That is the entire purpose of this checkpoint.
