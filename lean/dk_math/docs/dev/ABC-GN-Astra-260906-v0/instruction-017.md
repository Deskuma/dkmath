# instruction-017 — LUNA finite three-sector incidence ledger

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-017**.

LUNA-016 completely normalized the exceptional prime 3 at the theorem level:

~~~text
Sector A:
  3 does not divide a
  Coprime y T
  y^2 + 3 = 4*T*d^2

Sector B:
  3 divides a
  y = 3*y3
  T = 3*T3
  Coprime y3 T3
  3*y3^2 + 1 = 4*T3*d^2.
~~~

The arithmetic normalization is complete.

LUNA-017 should now freeze the **finite-set sector decomposition** and the
exact images/fibers of the normalized sector coordinates.

No counting estimate, density statement, or sparsity theorem is part of this
checkpoint.

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
report-016.md
report-015.md
report-014.md
report-013.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicThreeSector.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
~~~

Treat current production Lean as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-017.md.

Report exact finite-set definitions, equalities, partition/cardinality facts,
verification, and the remaining research boundary.

---

# Part I — fixed-T non-three sector fiber

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicThreeSectorIncidence.lean
~~~

For an existing fixed-T Pell-parameter fiber, define the non-three subfiber:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => ¬ 3 ∣ a)
~~~

Exact naming may be shortened, but keep the relation to the existing fixed-T
fiber explicit.

Provide the membership theorem:

~~~text
a in NonThreeFiber X D T
<->
a in PellParameterFiber X D T
and not 3 divides a.
~~~

Do not infer a cardinality bound.

---

# Part II — fixed-T three sector fiber

Define the exceptional subfiber:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => 3 ∣ a)
~~~

Provide the exact membership theorem.

Again, no cardinality estimate.

---

# Part III — exact disjoint sector partition

Prove:

~~~text
NonThreeFiber X D T ∪ ThreeFiber X D T
=
PellParameterFiber X D T.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_eq_nonThree_union_three
~~~

Also prove:

~~~text
Disjoint (NonThreeFiber X D T) (ThreeFiber X D T).
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_disjoint_three
~~~

Then prove the exact cardinal identity:

~~~text
(PellParameterFiber X D T).card
=
(NonThreeFiber X D T).card
+
(ThreeFiber X D T).card.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_card_eq_sector_cards
~~~

This is a finite partition only.

---

# Part IV — non-three sector packet consumer

For:

~~~text
a in NonThreeFiber X D T,
~~~

expose the LUNA-016 primitive packet directly:

~~~text
not 3 divides a
not 3 divides y
not 3 divides T

Nat.Coprime y T

y^2 + 3 = 4*T*d^2

Nat.Coprime y d

Squarefree T.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_packet
~~~

This should be a direct wrapper around

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet.
~~~

Do not duplicate the arithmetic proof.

---

# Part V — three-sector packet consumer

For:

~~~text
a in ThreeFiber X D T,
~~~

expose the normalized coordinates:

~~~text
3 divides a

y3 = GNExcessCubicThreeSectorY a
T3 = GNExcessCubicThreeSectorPellParameter T

2*a+3 = 3*y3
T = 3*T3

not 3 divides T3

Nat.Coprime y3 T3

3*y3^2 + 1 = 4*T3*d^2

Nat.Coprime y3 d.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_packet
~~~

This should consume the LUNA-016 reconstruction/equation/coprimality theorems.

Do not reprove them.

---

# Part VI — normalized three-sector parameter space

The original Pell parameter T is divisible by 3 on the three sector.

Define the finite image of the normalized parameter:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D
    |>.filter (fun a => 3 ∣ a))
    |>.image (fun a =>
      GNExcessCubicThreeSectorPellParameter
        (oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a))
~~~

A cleaner equivalent construction through the existing PellParameterSpace /
fixed-T fibers is acceptable.

The key point is that the represented normalized parameter is:

~~~text
T3 = T / 3.
~~~

Provide a membership theorem:

~~~text
T3 in ThreeSectorParameterSpace X D
<->
exists a in shellWitnessSpace X D,
  3 divides a
  and
  T3 =
    ThreeSectorPellParameter
      (oddPart (FullRepeatedModulus a) * Complement a).
~~~

Do not estimate the parameter-space cardinality.

---

# Part VII — normalized parameters are positive, squarefree, and prime-to-three

For:

~~~text
T3 in ThreeSectorParameterSpace X D,
~~~

prove:

~~~text
0 < T3
Squarefree T3
not 3 divides T3.
~~~

Recommended theorem packet:

~~~lean
GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_packet
~~~

The not-divisible-by-3 theorem is already in the LUNA-016 reconstruction for
each represented point.

For squarefreeness:

- original T is squarefree,
- T = 3*T3,
- T3 divides T,
- a divisor of a squarefree natural is squarefree.

Reuse standard squarefree divisor API.

Do not create new squarefree machinery.

---

# Part VIII — normalized three-sector witness fiber

Define the actual shell witnesses sharing a fixed normalized T3.

Recommended:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber
    (X D T3 : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a =>
      3 ∣ a ∧
      GNExcessCubicThreeSectorPellParameter
        (oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a) = T3)
~~~

Provide exact membership.

For every represented normalized T3, prove this fiber is nonempty.

No multiplicity bound.

---

# Part IX — exact partition of all three-sector witnesses by T3

Define the shell-level three-sector witness space if useful:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => 3 ∣ a)
~~~

This may be identified with the union over the original fixed-T ThreeFiber
objects.

Prove the exact normalized-parameter partition:

~~~text
(ThreeSectorParameterSpace X D).biUnion
  (fun T3 => ThreeSectorParameterFiber X D T3)
=
ThreeSectorWitnessSpace X D.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_eq_biUnion_parameterFibers
~~~

Prove pairwise disjointness of distinct T3 fibers.

Then prove:

~~~text
ThreeSectorWitnessSpace.card
=
sum T3 in ThreeSectorParameterSpace,
  ThreeSectorParameterFiber(T3).card.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessCount_eq_sum_parameterFiberCards
~~~

This is exact reindexing only.

---

# Part X — normalized fixed-T3 conic equation

For:

~~~text
a in ThreeSectorParameterFiber X D T3,
~~~

prove directly:

~~~text
3*(ThreeSectorY a)^2 + 1
=
4*T3*(evenPart (FullRepeatedModulus a))^2.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_equation
~~~

Also expose:

~~~text
Nat.Coprime (ThreeSectorY a) T3

Nat.Coprime (ThreeSectorY a)
  (evenPart (FullRepeatedModulus a)).
~~~

Recommended packet:

~~~lean
GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_primitive_packet
~~~

This should consume LUNA-016.

Do not count the normalized conic solutions.

---

# Part XI — non-three parameter space

The non-three sector does not require quotienting T.

If useful, define the represented non-three parameters directly:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellNonThreeParameterSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D
    |>.filter (fun a => ¬ 3 ∣ a))
    |>.image (fun a =>
      oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a)
~~~

For represented T prove:

~~~text
Squarefree T
not 3 divides T.
~~~

This part is optional.

The fixed-T non-three subfiber and normalized three-sector parameter ledger
have priority.

---

# Part XII — shell-level two-sector partition

Define, if not already done:

~~~text
NonThreeShellWitnessSpace X D
ThreeShellWitnessSpace X D.
~~~

Prove exact shell partition:

~~~text
NonThreeShellWitnessSpace ∪ ThreeShellWitnessSpace
=
shellWitnessSpace.
~~~

Prove disjointness and card identity:

~~~text
shellWitnessCount
=
NonThreeShellWitnessSpace.card
+
ThreeShellWitnessSpace.card.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_threeSector_split
~~~

This is the shell analogue of Part III.

No estimate of either term.

---

# Part XIII — extend the exact incidence ledger

By the end of LUNA-017, the finite ledger should include the sector split:

~~~text
shellWitnessCount
=
nonThreeShellCount + threeShellCount

and for each original T,

PellParameterFiber(T).card
=
NonThreeFiber(T).card + ThreeFiber(T).card

and

threeShellCount
=
sum T3 in normalizedThreeParameterSpace,
  normalizedThreeFiber(T3).card.
~~~

Record these together in the report.

Do not compare any term asymptotically.

---

# Part XIV — optional original-T to normalized-T3 map

On the original three sector, the map

~~~text
T -> T/3
~~~

is injective because all sector T satisfy 3 | T.

If a clean finite-set theorem is easy, prove the image of original
three-sector represented T values under division by 3 equals the normalized
T3 parameter space.

A possible theorem:

~~~text
image (fun T => T / 3) originalThreeSectorTSet
=
ThreeSectorParameterSpace X D.
~~~

This is optional.

Do not build a complicated auxiliary original-three-T set solely for this
corollary.

---

# Negative theorem boundaries

Document explicitly:

~~~text
The sector finite-set split is exact bookkeeping only.

The normalized three-sector parameter map is not assumed injective on
witnesses.

Fixed T3 is not assumed to have O(1) witnesses.

Neither sector is claimed sparse.

The normalized equation
  3*y3^2 + 1 = 4*T3*d^2
is not being counted here.
~~~

---

# What LUNA-017 is NOT

Do not attempt:

- any sector cardinality bound,
- any fixed-T or fixed-T3 multiplicity bound,
- Pell/conic solution counting,
- dyadic incidence sparsity,
- Hensel density,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce provider classes or unproved hypotheses.

This checkpoint freezes finite sector incidence only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicThreeSector
~~~

unless dependency order requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~text
lake build DkMath.ABC.GNExcessCubicThreeSectorIncidence
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

- fixed-T sector partition,
- fixed-T sector card identity,
- non-three packet consumer,
- three-sector packet consumer,
- normalized three-sector parameter space,
- normalized parameter support packet,
- normalized T3-fiber partition,
- normalized T3-fiber cardinal sum,
- normalized fixed-T3 primitive packet,
- shell-level sector card split.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-017.md
~~~

Title:

~~~text
# LUNA-017 — finite three-sector incidence ledger
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. fixed-T non-three sector fiber,
3. fixed-T three sector fiber,
4. exact disjoint partition,
5. fixed-T sector card identity,
6. non-three packet consumer,
7. three-sector packet consumer,
8. normalized T3 parameter space,
9. T3 positivity/squarefree/prime-to-three support,
10. normalized T3 witness fiber,
11. exact T3-fiber partition,
12. exact T3-fiber card sum,
13. normalized fixed-T3 primitive conic packet,
14. shell-level sector partition/card split,
15. optional original-T to T3 image status,
16. focused build,
17. ABC aggregator build,
18. no-placeholder / no-new-axiom result,
19. axiom audit,
20. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the theorem-level sector normalization from LUNA-016 has been
converted into exact finite incidence coordinates:

~~~text
fixed T fiber
=
non-three sector
disjoint union
three sector

and

three-sector witnesses
=
disjoint union over normalized T3
  fixed-T3 fibers.
~~~

Every normalized T3 fiber witness must expose:

~~~text
3*y3^2 + 1 = 4*T3*d^2

Coprime y3 T3

Coprime y3 d

Squarefree T3

3 does not divide T3.
~~~

Do not count any fiber.

After LUNA-017, both primitive sectors will be fully available as finite
objects ready for later arithmetic research.

That exact finite normalization, and no sparsity claim, is the entire purpose
of this checkpoint.
