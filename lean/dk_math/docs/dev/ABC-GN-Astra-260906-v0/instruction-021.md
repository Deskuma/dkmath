# instruction-021 — LUNA finite seven-depth incidence ledger

## Mission

Continue the ABC–GN campaign in fact-freezing / productionization mode.

This checkpoint is LUNA-021.

LUNA-020 completely normalized the paired cubic seven-sector at theorem level:

~~~text
forward-deep:
  a % 49 = 29

swap-deep:
  a % 49 = 22

shallow-seven:
  a % 7 = 1
  a % 49 != 29
  a % 49 != 22.
~~~

It also froze the exact repeated/complement and cross-gcd packets for all
three states.

LUNA-021 should convert that theorem-level normalization into exact finite
incidence objects over the existing shell witness space.

No state count, density estimate, relative-height theorem, or ABC closure is
part of this checkpoint.

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
report-020.md
report-019.md
report-018.md
report-017.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicSevenDepth.lean
DkMath/ABC/GNExcessCubicPairedSquareful.lean
DkMath/ABC/GNExcessCubicPairedOrientation.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
DkMath/ABC/GNExcessCubicRealizedDyadic.lean
~~~

Treat current production Lean as authoritative.

Do not include branch HEAD hashes or commit hashes in report-021.md.

---

## Part I — shell seven-sector witness space

Add a focused production module:

~~~text
DkMath/ABC/GNExcessCubicSevenDepthIncidence.lean
~~~

Define the shell-level seven-sector witnesses:

~~~lean
noncomputable def GNCubicPairedSevenSectorWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => a % 7 = 1)
~~~

Provide the exact membership theorem:

~~~text
a in SevenSectorWitnessSpace X D
<->
a in shellWitnessSpace X D
and a % 7 = 1.
~~~

No cardinality estimate.

---

## Part II — forward-deep state space

Define:

~~~lean
noncomputable def GNCubicPairedForwardSevenDeepWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 = 29)
~~~

Provide membership:

~~~text
a in ForwardDeepSpace
<->
a in shellWitnessSpace
and a % 49 = 29.
~~~

The explicit a % 7 = 1 condition may be omitted from the right-hand side if
derived from the residue.

Do not count the set.

---

## Part III — swap-deep state space

Define:

~~~lean
noncomputable def GNCubicPairedSwapSevenDeepWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 = 22)
~~~

Provide the exact membership theorem.

No counting statement.

---

## Part IV — shallow-seven state space

Define:

~~~lean
noncomputable def GNCubicPairedShallowSevenWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 != 29 and a % 49 != 22)
~~~

Use valid Lean syntax in the implementation.

Provide membership:

~~~text
a in ShallowSevenSpace
<->
a in shellWitnessSpace
and a % 7 = 1
and a % 49 != 29
and a % 49 != 22.
~~~

No residue-count theorem.

---

## Part V — exact three-way partition

This is the first main LUNA-021 deliverable.

Prove:

~~~text
ForwardDeepSpace
union
SwapDeepSpace
union
ShallowSevenSpace
=
SevenSectorWitnessSpace.
~~~

Recommended theorem:

~~~text
GNCubicPairedSevenSectorWitnessSpace_eq_threeState_union
~~~

Also prove pairwise disjointness of the three state spaces.

Recommended theorem family:

~~~text
GNCubicPairedForwardDeep_disjoint_SwapDeep
GNCubicPairedForwardDeep_disjoint_Shallow
GNCubicPairedSwapDeep_disjoint_Shallow
~~~

or one PairwiseDisjoint theorem if cleaner.

Then prove the exact cardinal identity:

~~~text
SevenSectorWitnessSpace.card
=
ForwardDeepSpace.card
+
SwapDeepSpace.card
+
ShallowSevenSpace.card.
~~~

Recommended:

~~~text
GNCubicPairedSevenSectorWitnessSpace_card_eq_threeState_cards
~~~

This is exact bookkeeping only.

---

## Part VI — state packet consumers

For membership in each state space, expose the LUNA-020 arithmetic packet
without requiring callers to separately supply residue hypotheses.

### Forward-deep

For a in ForwardDeepSpace X D, prove a packet containing:

~~~text
7 divides F
7 divides G
49 divides F
not 49 divides G

7 divides MF
not 7 divides MG

not 7 divides SF
7 divides SG

gcd(MF,SG)=7
gcd(SF,MG)=1
gcd(SF,SG)=1
gcd(MF,MG)=1.
~~~

Recommended:

~~~text
GNCubicPairedForwardSevenDeepWitnessSpace_packet
~~~

### Swap-deep

Expose the symmetric packet.

Recommended:

~~~text
GNCubicPairedSwapSevenDeepWitnessSpace_packet
~~~

### Shallow-seven

Expose:

~~~text
7 divides F
7 divides G
not 49 divides F
not 49 divides G

not 7 divides MF
not 7 divides MG

7 divides SF
7 divides SG

gcd(MF,SG)=1
gcd(SF,MG)=1
gcd(SF,SG)=7
gcd(MF,MG)=1.
~~~

Recommended:

~~~text
GNCubicPairedShallowSevenWitnessSpace_packet
~~~

These should be direct wrappers around LUNA-020.

Do not reprove the arithmetic.

---

## Part VII — repeated-product deep-state space

Define the seven-sector shell witnesses for which the paired repeated product
carries 7:

~~~lean
noncomputable def GNCubicPairedRepeatedProductSevenWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a =>
      7 ∣ GNCubicForwardRepeatedPart a *
        GNCubicSwapRepeatedPart a)
~~~

Prove exact set equality:

~~~text
RepeatedProductSevenWitnessSpace
=
ForwardDeepSpace union SwapDeepSpace.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedProductSevenWitnessSpace_eq_deep_union
~~~

This should consume:

~~~text
seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState.
~~~

Because the paired repeated product is squarefull, the same set may also be
characterized by 49-divisibility if clean.

Do not infer any density.

---

## Part VIII — shallow state as repeated-product complement

Characterize:

~~~text
a in SevenSectorWitnessSpace
and not 7 divides MF*MG
<->
a in ShallowSevenSpace.
~~~

Recommended theorem:

~~~text
GNCubicPairedShallowSevenWitnessSpace_iff_not_repeatedProductSeven
~~~

A set equality is also acceptable.

This makes the trichotomy visible from the paired repeated product alone:

~~~text
deep iff 7 enters MF*MG;
shallow iff 7 stays out of MF*MG.
~~~

No size conclusion.

---

## Part IX — optional state label type

If useful, define a small finite state type:

~~~text
forwardDeep
swapDeep
shallow
~~~

and a classification function for seven-sector shell witnesses.

This is optional.

Only add it if it clearly improves the finite-set API.

The three concrete Finset definitions are the required deliverable.

---

## Part X — optional residue image

Define the actual mod-49 residue image if useful:

~~~lean
noncomputable def GNCubicPairedSevenSectorResidueSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).image
    (fun a => a % 49)
~~~

Prove every represented residue belongs to:

~~~text
1, 8, 15, 22, 29, 36, 43.
~~~

Do not prove all seven residues occur.

Do not infer equidistribution.

This part is optional.

The three state spaces have priority.

---

## Part XI — shell cardinal ledger extension

At minimum expose:

~~~text
SevenSectorWitnessSpace.card
=
ForwardDeep.card + SwapDeep.card + Shallow.card.
~~~

If cheap, also expose:

~~~text
RepeatedProductSevenWitnessSpace.card
=
ForwardDeep.card + SwapDeep.card.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedProductSevenWitnessSpace_card_eq_deep_cards
~~~

No bound on any card.

---

## Part XII — optional square-cube consumers

Use LUNA-019 only as wrappers.

For forward-deep and swap-deep witnesses, expose:

~~~text
squarefull MF
squarefull MG

MF*MG
=
(uF*uG)^2 * (rF*rG)^3

Squarefree (rF*rG)

MF*MG divides 3*(a+1)^4 + a^2.
~~~

For shallow-seven, expose the same packet together with:

~~~text
not 7 divides MF*MG.
~~~

Recommended packet names:

~~~text
GNCubicPairedForwardSevenDeep_squareCube_packet
GNCubicPairedSwapSevenDeep_squareCube_packet
GNCubicPairedShallowSeven_squareCube_packet
~~~

These are optional convenience consumers.

Do not infer height-relative size.

---

## Part XIII — no state counting

Document explicitly:

~~~text
The three state spaces are exact finite filters.

No theorem compares their cardinalities.

The two deep residues being single mod-49 classes does not by itself produce
the global density estimate needed for ABC.

Higher 7-adic depth remains unrestricted inside the forward-deep or swap-deep
state.
~~~

---

## What LUNA-021 is NOT

Do not attempt:

- counts or asymptotics of the three states,
- equidistribution modulo 49,
- higher 7-adic depth counting,
- paired relative-height exclusion,
- shell-count bounds,
- Hensel rarity,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce providers or unproved hypotheses.

This checkpoint freezes finite seven-state incidence only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicSevenDepth
~~~

Do not reorder unrelated imports.

---

## Verification

At minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicSevenDepthIncidence
lake build DkMath.ABC
~~~

Scan changed production files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit principal declarations, especially:

- three state-space memberships,
- exact partition,
- disjointness,
- card identity,
- state packet consumers,
- repeated-product deep-space equality.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-021.md
~~~

Title:

~~~text
# LUNA-021 — finite seven-depth incidence ledger
~~~

Report:

1. files changed,
2. seven-sector shell witness space,
3. forward-deep space,
4. swap-deep space,
5. shallow-seven space,
6. exact three-way partition,
7. pairwise disjointness,
8. exact cardinal split,
9. state packet consumers,
10. repeated-product-seven witness space,
11. deep-union equality,
12. shallow complement characterization,
13. optional residue image status,
14. optional square-cube consumers,
15. focused build,
16. ABC aggregator build,
17. forbidden-construct result,
18. axiom audit,
19. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the theorem-level mod-49 trichotomy from LUNA-020 has become exact
finite incidence geometry:

~~~text
SevenSectorWitnessSpace
=
ForwardDeep
disjoint union
SwapDeep
disjoint union
ShallowSeven

and

RepeatedProductSevenWitnessSpace
=
ForwardDeep
disjoint union
SwapDeep.
~~~

Each state-space witness must expose its exact repeated/complement and cross-gcd
packet from LUNA-020 without requiring new arithmetic hypotheses.

Do not count the states.

After LUNA-021, the prime-7 paired-orientation structure will be fully
available both theorem-wise and as finite shell objects.
