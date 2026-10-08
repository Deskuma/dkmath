# Instruction012 implementation report

Exact head/tail cancellation and root11 are formalized. Seven prime anchors,
including1009 and1013, have structural head proofs and independent direct rough
wave proofs. The quantitative advance is a min-free surviving-wave currency;
the elementary maximum-multiplicity estimate remains too coarse. This is a
finite checkpoint result, with a uniform provider still missing.

## 1. Exact partition of the existing canonical incidence

`canonicalRootHead n P` and `canonicalRootTail n P` are complementary filters
of `paritySafeCanonicalQuotientCoSupportIncidences n`. Their conditions are
root<=P and P<root. `supportExcess_eq_head_add_tail` proves E=H+T.
`canonicalRootHead_card_eq_root_sum` identifies H with the sum of the old root
fibers over actual active primes p<=P. No new E ledger is introduced.

## 2. Root>P and actual small-prime avoidance

`canonicalRoot_gt_iff_rough` proves the equivalence at a covered candidate.
Active prime labels and endpoint <=P are retained. For empty support the
canonical default is0, although the seat may be rough; the covered hypothesis
is essential. The exact min-free `mem_canonicalRootTail_iff` consists of a
rough candidate r, a supported secondary q, and existence of a smaller
supported active label a<q. That last condition preserves canonical erasure.
The bare object proposed in phase3 counts the root too and is full rough
incidence, rather than the excess tail.

Smallest active-shell regressions are n4,r5,point21,q3,P0 for the erased root,
and n4,r1,point17,P0 for empty support. Cutoffs below3 cause no incorrect
minimum inference.

## 3. Secondary regrouping and safe Nat cancellation

`canonicalRootHead_card_eq_secondary_sum` regroups H over the same actual
active-q index as B2. `canonicalHeadAtQ_card_eq_pair_sum` equals the ordered
sum of p<=P,p<q root-pair charges. The pointwise theorem proves
Head(q)+Tail(q)<=cap(q), then Tail(q)<=cap(q)-Head(q). Only after this proof does
`canonicalRemainingCap_eq_secondary_sum` distribute Nat subtraction.

For every anchor the exact identity is

    RemainingCap = covered.card + tail.card + (B2-I).

Thus neither termwise residual nor its sum is the excess tail alone. The
smallest active shell n4,P3,q3 has head0,tail0,cap1, so residual1!=tail0. The
regression is kernel-checked. The relation keeps I, E and B2 distinct.

`ParitySafePrimeAnchorCap` additionally proves, for an odd prime anchor only,
that cap(q)=`primeAnchorProductWaveCount n q`=actual q-wave card. The singleton
anchor prime-factor set supplies the complete coprimality exclusion, and the
spacing/min caps are squeezed between this exact count and the old actual-wave
lower bound. Consequently `primeAnchorTwoPrimeUpper_eq_incidence` proves
B2=I in this scope. `primeAnchorHead_gap_iff_rough` then proves for every cutoff:

    B2 < A+Head  iff  roughI < roughSeats.card.

For odd prime anchors RemainingCap=covered.card+tail.card. This exactness is
derived, not an assumption about the general B2 cap.

## 4. Exact root11 inclusion-exclusion

Write W(m) for the candidate product wave cardinality, retaining parity and
anchor coprimality. For prime n>11 and active q>11:

    root11Pair(q) = W(11q)+W(165q)+W(231q)+W(385q)
                     - (W(33q)+W(55q)+W(77q)+W(1155q)).

All pair credits are restored before Nat subtraction. The neutral
`DkMath.NumberTheory.card_filter_three_exclusions` proves this combinatorics
for any finite carrier and three decidable predicates. The triple term is a
cost. `canonicalRootCharge11_eq_fiber` turns the sum over q>11 of corrected
floor counts into the old root11 fiber. A triply excluded singleton rejects
sequential clipped subtraction: correct result0, naive result2.

`root11_sieve_eq_floor_union` in the regression harness formally identifies
`canonicalRootSieveLower n 11` with the floor union estimate. Its exact lost
credit is kernel-checked:

|n|exact C11|old union lower|lost credit|
|---|---|---|---|
|47|1|1|0|
|97|3|3|0|
|127|2|2|0|
|211|4|4|0|
|503|8|7|1|
|1009|27|21|6|
|1013|49|46|3|

A neutral three-exclusion theorem and the cutoff11 extension suffice; an
arbitrary powerset inclusion-exclusion API was not needed for these proofs.

## 5. Cumulative charges at every required anchor

A is actual candidate cardinality; B2 is the old structural cap; D=B2-A+1.
The head values come from exact floor/product-wave formulas, not full E/I.

|n|A|B2|D|C<=3|C<=5|C<=7|C<=11|least tested cutoff|
|---|---|---|---|---|---|---|---|---|
|47|46|54|9|12|16|20|21|3|
|97|96|125|30|29|39|46|49|5|
|127|126|170|45|42|53|58|60|5|
|211|210|307|98|78|105|120|124|5|
|503|502|813|312|222|300|336|344|7|
|1009|1008|1702|695|460|608|684|711|11|
|1013|1012|1721|710|461|620|699|748|11|

`root_charges_checked`, `caps_checked`, `head_charges_checked` and
`checkpoints_uncovered_from_head` verify this route.1009 has711>=695 and1013
has748>=710. Their independent `shell1009_prime` and `shell1013_prime`
endpoints use the direct rough formulas below.

## 6. Least tested cutoffs and growth diagnostics

The least tested cutoffs among3,5,7,11 are3,5,5,5,7,11,11 in table order.
`cutoff_checked` checks failure at all smaller tested cutoffs and success at
the selected one. It also checks P²<=n and P<=n. For natural P these imply
P<=sqrt(n), but no uniform cutoff growth or constant-cutoff sufficiency is
inferred. Cutoffs13 and larger were not part of the demand search.

## 7. Exact rough-seat and incidence counts

`canonicalRoughCandidates` includes empty-support seats. `canonicalRoughWave`
retains every supported q, including the root. The exact identities are

    roughI = sum over rough seats of support.card = roughCovered.card + T;
    RemainingCap + roughSeats.card = A + roughI + (B2-I).

Hence RemainingCap<A iff roughI+(B2-I)<roughSeats.card. Also, the direct
consumer `uncovered_nonempty_of_roughWave_sum_lt` requires only
roughI<roughSeats.card. This is stronger than a bare seat-count estimate and
uses all supported q labels explicitly.

Let F(m)=the three-exclusion floor count at modulus m, removing3/5/7 using
single costs, pair credits and triple cost. Exact cutoff11 formulas are

    roughSeats11.card = F(1)-F(11);
    roughWave11(q).card = F(q)-F(11q),  q>11;
    roughI11 = sum over active q>11 of (F(q)-F(11q)).

Active waves q<=11 are empty. `prime_squareCell_of_roughEleven_count` turns
the strict floor comparison into a prime in SquareCell n. At all seven anchors
roughI11<roughSeats11; the margins are13,20,16,27,33,17,39. The formula does
not compute min', full E, or full I.

Candidate seat counts at all cutoffs are kernel-checked by finite avoidance;
all four have generic product-wave floor identities. Cutoff3 is W(1)-W(3),
cutoff5 is W(1)+W(15)-(W(3)+W(5)), and cutoff7 is F(1); the first two exact
formulas are also checked in the regression harness. Cutoff11
incidence in the following table is checked through the structural floor sum.

|n|rough seats3|rough seats5|rough seats7|rough seats11|roughI11|tail11|
|---|---|---|---|---|---|---|
|47|30|24|21|20|7|0|
|97|64|51|44|39|19|2|
|127|84|67|58|52|36|7|
|211|140|112|96|88|61|15|
|503|334|267|229|208|175|48|
|1009|672|537|460|419|402|134|
|1013|674|539|462|421|382|108|

Actual tails are separate diagnostics in `LegendreCanonicalTailDiagnostics`,
with numerical checks cached in `LegendreCanonicalTailDiagnosticCounts`:

|n|tail3|tail5|tail7|tail11|D-head3|D-head5|D-head7|D-head11|
|---|---|---|---|---|---|---|---|---|
|47|9|5|1|0|0|0|0|0|
|97|22|12|5|2|1|0|0|0|
|127|25|14|9|7|3|0|0|0|
|211|61|34|19|15|20|0|0|0|
|503|170|92|56|48|90|12|0|0|
|1009|385|237|161|134|235|87|11|0|
|1013|395|236|157|108|249|90|11|0|

The last four columns use clipped Nat subtraction. The finite cutoff11 rough-covered seat counts are checked separately. The
already checked floor roughI and roughI=roughCovered+tail give tail11; then
E=head11+tail11 and the structural heads recover all four actual tail cards.
The full-support diagnostic normal form is retained, and its values are proved
through these identities rather than directly evaluating whole E. The
diagnostic module imports the structural calibration; the structural prime
proofs cannot depend on diagnostic evaluations.

## 8. Elementary rough support multiplicity

`activeSupport_prod_dvd_point` proves product of distinct actual support labels
divides n²+r at a candidate seat. If every active label above P is at least L,
`rough_support_pow_le_point` proves L^support.card<=n²+r<=n²+2n. With1<=L and
n²+2n<L^(K+1), `rough_support_card_le` proves support.card<=K. Consequently:

    T <= roughSeats.card * (K-1);
    roughI <= roughSeats.card * K.

No logarithms occur. The first bound counts erased-root multiplicity and the
second retains the root. A seat count alone cannot control tail multiplicity:
at prime anchor19,offset24,cutoff3,point385 has support{5,7,11}, hence one seat
contributes two tail labels. This counterexample is kernel-checked.

The independent discovery calculation illustrates the coarse cutoff11 bound
L=13 (these K/upper values are arithmetic diagnostics, not extra checked Lean
numerical endpoints):

|n|power-threshold K|roughSeats11*(K-1)|actual tail11|
|---|---|---|---|
|47|3|40|0|
|97|3|78|2|
|127|3|104|7|
|211|4|264|15|
|503|4|624|48|
|1009|5|1676|134|
|1013|5|1684|108|

Even a proved roughI<=K*roughSeats cannot imply roughI<roughSeats when K>=1.
Sharper average multiplicity or direct surviving-q wave estimates are needed.

A further uniform elementary result is already proved, without a prime-anchor
hypothesis. At P=Nat.sqrt n, L=P+1 satisfies

    n+1 <= L²,  hence n²+2n < (n+1)² <= L⁴.

`sqrtCutoff_power_four_gt`, `sqrtCutoff_support_card_le_three` and
`sqrtCutoff_tail_card_le_two_mul` therefore prove support.card<=3 and
T<=2*roughSeats.card at every sqrt-cutoff rough candidate. This proves a
multiplicity scale, not uniform demand sufficiency. The support bound3 is
sharp: prime anchor19,offset24,cutoff sqrt19=4 has support{5,7,11}, as checked
by `sqrt_multiplicity_bound_sharp`. Thus a global maximum bound2 cannot replace
an average or intersection estimate.

## 9. Does cancellation provide leverage beyond appending roots?

Yes, on these finite checkpoints. Root11 alone extends the head hierarchy,
while the new direct rough currency supplies a distinct proof independent of
head charges and B2. In particular1009/1013 are both solved by min-free
surviving-wave floor inequalities402<419 and382<421. The exact head/rough
identity isolates cap slack for general anchors, and the new odd-prime cap
exactness theorem proves that this obstruction vanishes at prime anchors. The elementary maximum-multiplicity bound alone does not deliver this
quantitative gain, and the seven finite rows do not establish asymptotics.
The odd-prime head-gap and rough-gap tests are logically equivalent, not a
strictly stronger inequality. The advance is the proved exact currency and its
min-free floor provider; its numerical margins agree with the head margins.

## 10. Missing uniform theorem and next implementation proposals

A precise next candidate uses the independent cutoff P(n)=Nat.sqrt n and
threshold n0=1013. This is a proposed starting threshold; the finite table
does not justify it. Prove, for every prime n>1013:

    sum over active q of (canonicalRoughWave n (Nat.sqrt n) q).card
      < (canonicalRoughCandidates n (Nat.sqrt n)).card.

This is a proposed uniform provider, not a result or conjecture asserted by
this implementation. The cutoff is specified without evaluating E. The
existing generic direct consumer would finish the prime-anchor square-cell
claim from it. The head-demand alternative is the corresponding cumulative
structural root charge bound >=B2-A+1, with the required B2>=A hypothesis when
rewriting that Nat demand equivalence. Neither uniform inequality is proved.
These targets address prime anchors only; extending to all integer anchors
would require a separate argument.

Next implementation proposals, in dependency order:

1. Add a finite small-prime avoidance floor provider indexed by the actual
   cutoff set; expose odd and anchor corrections as reusable carry identities.
   At cutoff13, reuse the existing three-exclusion F as a carrier count and
   delete11/13 with the neutral two-exclusion identity:
   G(m)=F(m)+F(143m)-(F(11m)+F(13m)). This is an explicit next finite provider,
   requiring the corresponding coprimality/filter bridges; it needs no generic
   powerset API. Then compare exact growth against Bonferroni truncation.
   Also prove the incremental cutoff identity for P<=Q:
   Head(Q)-Head(P)=(roughI(P)-roughI(Q))-(R(P)-R(Q)). The required Nat safety
   is justified by every removed rough seat having nonempty support, hence the
   removed incidence count is at least the removed seat count. This proposed
   API would compute new head charge without introducing another min selector.
2. Implement the large-label moment bridge at P=Nat.sqrt n. Since support has
   at most3 labels, unordered rough pair incidence M2 and triple incidence M3
   should satisfy T=M2-M3 and uncovered.card=R+M2-(roughI+M3), with costs/credits
   combined before Nat subtraction. These formulas are next implementation
   targets, not Lean results in this checkpoint. They follow seatwise from
   k in{0,1,2,3}; higher intersections vanish by the proved product threshold.
   A consumer R+M2>roughI+M3 can recover triple credit and is weaker than the
   current sufficient roughI<R test. Large-label pair products exceed n,
   giving a natural route to the existing quotient endpoint/carry APIs.
   Prove maps before importing old near-triple/far-key carrier capacities.
3. Refine the support-product estimate using distinct ordered prime lower
   labels, or prove an average multiplicity estimate. The bound L^k is too
   coarse at1009/1013; a maximum bound alone cannot solve the strict rough
   incidence comparison.
4. State the explicit sqrt cutoff uniform provider as an isolated theorem
   contract with a proved consumer and finite regressions. Establish uniform
   surviving-wave/carry estimates before promoting any threshold or scale.

No Legendre conjecture, uniform T=1, PNT/RH, analytic sieve estimate, or FLT/ABC
consequence is claimed. Validation and complete dependency audits are recorded
in [validation](validation-012.md); source decisions and successive checkpoints
are in [source inventory](source-inventory-012.md) and [findings](findings-012.md).

Outcome A — HEAD/TAIL CANCELLATION GAINS NEW LEVERAGE
