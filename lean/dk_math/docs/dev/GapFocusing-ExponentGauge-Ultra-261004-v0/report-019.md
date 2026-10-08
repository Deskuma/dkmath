# Report 019 - phased PrimeWorld packets and coarse streets

The new result is an exact finite assignment frontier at an arbitrary square
anchor, with period width M rather than anchor width n. It connects the 018
odd-gap radical to existing PrimeWorld residues, keeps the square-point
phase, and exposes actual outside-prime incidence constraints. A universal
full-cover contradiction has not been proved.

Implementation: [PrimeWorldPacketBridge](../../../DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean),
[CoarsePrimorialTown](../../../DkMath/NumberTheory/Legendre/CoarsePrimorialTown.lean),
[CrossPeriod](../../../DkMath/NumberTheory/Primitive/CrossPeriod.lean).
The original PacketCross collision theorem delegates to the neutral helper;
its public proposition is unchanged. The facade imports were added after the
focused build succeeded. The new Lean files and modified PacketCross use the
standard copyright/author header and import-adjacent file marker.

## 1. Broad discovery and previously unnamed APIs

The pre-implementation [source inventory](source-inventory-019.md) lists exact
declarations from the required islands and records historical exclusions.
Discovery also found PrimorialUniverse.squareShellWheelProjection and
PrimorialUniverse.forall_raw_lift_digit_realized_by_canonical_orbit,
SquareAnchorPrimeSignCRT, FreshCollisionMatching, and the continuous
StructuralArithmetic.CosmicSquareScaling API. No exact arbitrary-anchor
coarse-street implementation or maximal fitting primorial selector was found.
The actual provider facade is NumberTheory.PrimorialUniverse, not
Primitive.PrimorialUniverse.

PeriodicPrimeWorld and PrimeWorldResidues supply observer periodicity and
refinement. CoprimePacket supplies the packet totient cardinality.
PacketCross already supplies the n-shift transpose and product-period
sparsity. Those facts were reused rather than recreated as independent
number-theory claims. Primitive imports no Legendre modules.

The historical mixed-radix audit realizes every admissible raw coordinate.
The square-shell-wave-transport audit rejects descent from shifted offsets
outside a smaller shell. FreshCollisionMatching's smaller cofactors and
endpoint uniqueness do not supply a strict capacity inequality. None of
these negative audits is reversed here.

## 2. Exact residue-to-packet adapter

primeWorldResidues_eq_packetBase proves exact finite-set equality when
1 < M, where M = primeWorldModulus S. The range representatives exclude zero
by coprimality; the Icc representatives exclude M by the same condition.
card_primeWorldResidues_eq_totient uses the existing packet cardinality.
primeWorld_totient_insert rewrites the existing fresh-prime recurrence into
this dictionary. It is an adapter, not a new totient calculation.

## 3. Modulus-one exception

primeWorld_packet_modulus_one_mismatch is kernel checked:

```text
primeWorldModulus empty = 1
primeWorldResidues empty = {0}
squareAnchorCoprimeBaseOffsets 1 = {1}
```

Their cards agree, but their finite sets do not. Equality/image adapters
retain 1 < M. Street cardinality itself needs no such guard. Certified worlds
have positive modulus; M <= n then already implies a positive anchor.

## 4. The 018 odd-gap world

centeredOddGapPrimeWorld n abbreviates primeScalesUpTo(2*n-1) with 2 erased.
knownPrimeScales_centeredOddGapPrimeWorld certifies it.
centeredOddGapPrimeWorld_eq_primeFactors and
centeredOddGapPrimeWorld_modulus_eq_radical reuse the 018 support theorem.
centeredOddGapPrimeWorld_residues_eq_packet is its guarded packet dictionary.
No second radical, primorial product, or prime-factor arithmetic is defined.

## 5. Square-point phase

supportDisjointFrom_iff_squareShell_address identifies survival with
membership of the existing squareShellWheelProjection in primeWorldResidues.
The address is (n^2+r) mod M throughout. This even handles the empty world
without imposing the positive open-wheel convention of WheelSurvivor.

The regression at n=4 and S={2,3} gives phased base {1,3}, whereas the offset
unit base modulo 6 is {1,5}. Their difference is real.
coarsePrimeWorldBase_eq_packet_of_modulus_dvd_anchor removes the phase only
with an explicit M-divides-n hypothesis.

## 6. One-period base and square-window embedding

coarsePrimeWorldBase filters Icc(1,M) by Coprime(n^2+r,M).
card_coarsePrimeWorldBase applies the existing translated complete-period
count. image_coarsePrimeWorldBase_address and
existsUnique_coarsePrimeWorldBase_address prove that every canonical residue
appears exactly once. The finite injection uses congruence cancellation and
an offset difference smaller than M. There is no M-divides-n premise.

coarsePrimeWorldBase_squareOffsets proves that both r and M+r belong to the
square window whenever M <= n. The generic API takes an explicit certified
finite world, so it also works for worlds that are not initial prime segments.

## 7. Periodic shift and two streets

coarsePrimeWorldShift is the injective image r -> M+r, and
coarsePrimeWorldTown is the union. disjoint_coarsePrimeWorldStreets,
card_coarsePrimeWorldShift, card_coarsePrimeWorldTown, and
coarsePrimeWorldTown_squareOffsets give disjoint streets of equal size with
union card 2*totient(M). coarsePrimeWorld_survivor_shift delegates directly
to PeriodicPrimeWorld. coarsePrimeWorld_address_shift proves equal addresses.
These statements use the actual gap M. They do not identify an arbitrary
coarse pair with the literal n-shift packet of CoprimePacket.

## 8. Complete-point and factor coprimality

coprime_coarsePrimeWorldPoints reduces gcd(A,A+M) to gcd(A,M)=1, where
A=n^2+r. not_prime_dvd_both_coarsePoints excludes a shared prime.
coprime_coarsePoint_factors applies the existing Coprime.of_dvd primitive to
any supplied opposite-side factors, including complementary quotients.
coarse_packet_oldSupport_family feeds each individual pair into the existing
family predicate. A union of these local certificates is not a global
certificate: different packets can share a support prime.

## 9. Full-cover assignment package

coarse_survivor_support_outside puts every actual old support in
T = primeScalesUpTo n minus S. prime_outside_not_dvd_coarseModulus certifies
that a prime outside the known prime world does not divide M.
exists_distinct_coarseOutside_cover_pair supplies distinct directions in T
for both sides of each base representative under full cover.

No S-subset-old premise is needed: removing even a larger certified world
still gives the exact implication that any surviving old support is outside
S. The support containment, embedding, and pair coprimality are explicit.
There are exactly totient(M) base packets, but the number of incidences can
be larger. coarseCrossCount_eq_support_products is the exact transpose of
actual Cartesian supports. totient_le_coarseCrossCount_of_fullyCovered gives
the necessary lower bound. At n=42, S={3,5}, eight packets have ten incidences.

## 10. Fixed ordered-pair occupancy

crossPeriod_mul_dvd_diff is neutral arithmetic, extracted from PacketCross.
Both the old specialization and coarseCrossOffsets_mul_dvd_diff use it.
Distinct prime directions give coprime p,q and hence p*q divides the offset
difference between two hits. card_coarseCrossOffsets_le_one uses width M:
when M < p*q, a fixed ordered pair hits at most one representative.

The near multiplicity is essential. A kernel regression proves more than one hit
for p=2, q=11 at n=M=105, S={3,5,7}. The diagnostic fiber is offsets
13,79,101. Their product period 22 fits inside the width and cannot be
treated as capacity one.

## 11. Near/far decomposition and comparison

coarseNearPairs and coarseFarPairs split by p*q <= M and M < p*q.
coarseNear_union_far and disjoint_coarseNear_far prove the exact partition;
coarseCrossCount_eq_near_add_far gives exact incidence decomposition.
coarseFar_sum_le_card bounds the far contribution by available far ordered
pairs. The resulting necessary condition is coarseTown_assignment_frontier:

```text
full cover and M <= n imply
  totient(M) <= near incidence + number of far ordered outside pairs.
```

For M <= n, the far criterion is available for products in (M,n] that the
old width-n bound does not classify as far. This is a sharper local width
criterion on a different packet family, not a globally stronger capacity
bound for the original n-shift packets. There is no valid inequality
2*packet_count <= card(T) without controlling reuse across packets.

## 12. Canonical fitting level and bounded experiment

No existing canonical maximal fitting primorial provider was found. No
production selector or global choice was added. The experiment chooses the
largest initial product fitting below n, once with 2 included and once with
2 excluded. These are operational choices in Python; production assumes
M <= n explicitly. A universal selector with maximality and next-refinement
bounds remains a separate possible adapter, not a capacity theorem.

The [diagnostic data](evidence/MANIFEST.md#log-bba424f576f97885) has 602 rows: n=1..300 and 1031,
for both worlds. It records S, cutoff, M, residue and street cards, T card,
whole-shell and town escapes, actual covered packets, incidences, near/far
counts and sums, maximum occupancy, coprime pair count, original n-packet
count, greedy support-disjoint families, and inherited 018 fold statistics.

Selected rows are exact integer diagnostics, not Lean theorems:

| n | World | M | Packets | T | Incidence | Near/Far pairs | Max occupancy | Greedy family / old primes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | initial | 2 | 1 | 2 | 0 | 0/2 | 0 | 2/3 |
| 8 | initial | 6 | 2 | 2 | 0 | 0/2 | 0 | 4/4 |
| 11 | initial | 6 | 2 | 3 | 0 | 0/6 | 0 | 4/5 |
| 19 | odd | 15 | 8 | 6 | 3 | 2/28 | 1 | 9/8 |
| 29 | odd | 15 | 8 | 8 | 6 | 2/54 | 1 | 8/10 |
| 297 | initial | 210 | 48 | 58 | 39 | 6/3300 | 1 | 63/62 |
| 1031 | initial | 210 | 48 | 169 | 60 | 6/28386 | 1 | 63/173 |
| 1031 | odd | 105 | 48 | 170 | 106 | 22/28708 | 2 | 40/173 |

Maximum incidence/packet pressure is 106/48 in the last row. Minimum ordered
direction-count slack is -2 at n=3, odd world {3}, where T={2} has no distinct
ordered pair. Neither statistic is an asymptotic estimate.

## 13. Existing capacity consumer and missing global certificate

A regression constructs the entire n=6, S={2,3} town {1,5,7,11} as an actual
PairwiseOldSupportDisjointSquareSeatFamily. Its four seats exceed the three
old primes. six_prime_via_existing_capacity_consumer immediately applies
exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies.
No new capacity consumer is introduced.

This finite certificate uses already empty actual supports. Similarly, the
scan's n=297 family of size 63 includes already uncovered seats. It is useful
finite validation, not an independent universal supply of capacity.
The kernel counterexample at n=3, S={3} shows that individual pair coprimality
does not make the whole town support-disjoint: offsets 1 and 5 share prime 2.
The remaining requirement is cross-packet collision control sufficient to
construct a large global separated subfamily, or an independently proved
assignment deficit. Far ordered-pair uniqueness controls each (p,q), not
reuse of a single p with several different partners.

## 14. Genuine interaction with 018

Category B as a conditional carrier reduction:
centeredOddGap_survivor_covered_only_two excludes every old odd cover
direction in the full same-anchor odd-gap world; an odd survivor is
uncovered. This is the chosen world's exact support content, not a new
independent fold invariant. Existence of an embedded survivor is not
supplied when the radical exceeds n. At n=3
that radical is already 15. The bounded data records this product explicitly;
it never assumes the full same-anchor odd world fits.

Category C for the order-four dictionary: coarse_visibleNorm_direction
retains p outside S, p mod 4 = 1, and the exact order-four address when an
actual coarse support direction also divides the centered norm. It does not
restrict unrelated outside directions. Consecutive centered norm/aggregate
coprimality concerns different anchors, while the two streets stay at one
anchor with gap M. It gives no new cross-packet capacity here. Smaller odd
worlds from another cutoff can fit, but then the same-anchor complete odd
exclusion no longer applies to all old directions.

## 15. Prime-power floor sum

No consumer required the deferred theorem
centeredFoldGcdProduct_padicVal_eq_primePowerFloorSum. It remains deferred.
Exact valuations from 018 are reused only as diagnostic fold statistics.
Deepening them would not repair the cross-packet support-reuse gap.

## 16. Narrowest remaining bridge and next implementation proposal

The established frontier still needs a strict deficit or a sufficiently
large global support-disjoint subfamily. Neither is proved for arbitrary n.
The next bounded implementation should measure the precise cross-packet
loss rather than presume each outside direction is available only once.

Proposed module: CoarseTownSupportPacking. Define E as ordered r<s in the
actual town whose old supports intersect. Prove, for any finite town, that
there exists R contained in the town with pairwise disjoint actual supports
and the exact finite deletion bound:

```text
town.card <= R.card + E.card.
```

A finite induction can delete one endpoint of a remaining collision and
charge the deletion to a distinct removed edge. This is a combinatorial
packing statement valid independently of full cover, not Legendre rewritten
as a provider hypothesis. Combine its shell certificate with the existing
capacity consumer only when the separately checked numerical inequality
old_prime_card + E.card < town.card holds. First compare the bound with the
602 existing rows and preserve the n=3 reuse regression. Do not claim that
this weak edge bound will succeed uniformly; a stronger packing rule may be
needed. An optional refinement should compute exact prime-fiber repetition
and CRT phases for the actual width M, using existing PrimeAddress APIs.
No valuation floor sum or general Hall framework is required for this pass.

A separate continuous proposal belongs outside this capacity route.
Analysis.GapFill already provides gapLine/gapFill and endpoint/interval
identities; DkReal provides interval and semantic Real machinery.
StructuralArithmetic.cosmicSquareImage supplies sqrt(1+y)-1 and quadratic
reconstruction. The missing thin adapter for x>0 is the rescaled expression
u=sqrt(x^2+k)-x with k>=0, proving u>=0 and u^2+2*x*u=k. With x,k,j natural and x>0, its proposed integer landing
statement is u = real_cast(j) exactly when k=2*x*j+j^2. This would explain continuous gnomon quantization; it supplies no
prime-cover obstruction. No new real-analysis implementation was made here.

[Validation](validation-019.md) records the focused, facade, root, regression,
public axiom, source, and parser-safe artifact checks.

Outcome B - COARSE PRIMORIAL TOWN YIELDS A NEW EXACT ASSIGNMENT FRONTIER
