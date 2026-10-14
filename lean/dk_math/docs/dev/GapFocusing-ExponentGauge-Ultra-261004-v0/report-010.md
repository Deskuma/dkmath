# Instruction 010 — merged CRT families and demand scaling

Noninjective family indices now feed the original support-excess ledger through witness unions at actual seats. Mixed-anchor candidate CRT and counted lift families are proved. A small controlled basis solves24 of the25 previous survivors; adding23,29,31 at97 supplies the remaining certificate. The same expansion supplies prime conclusions at107 and127. Fixed-pool scaling remains limited: neither tested basis meets demand at211 or503.

This is a bounded demand-scaling audit with reusable production theorems. It does not prove Legendre's conjecture, uniform charge sufficiency, or analytic growth estimates.

Evidence: [source inventory](source-inventory-010.md), [findings](findings-010.md), [validation](validation-010.md), [merged production](../../../DkMath/NumberTheory/Legendre/ParitySafeMergedCRT.lean), [mixed/scaling production](../../../DkMath/NumberTheory/Legendre/ParitySafeMixedCRT.lean), [bounded data](evidence/MANIFEST.md#log-7fc348be1b1902cb), [diagnostic proofs](../../../DkMathTest/NumberTheory/LegendreMergedCRT.lean), [counterexamples and lift regressions](../../../DkMathTest/NumberTheory/LegendreMergedCRTRegression.lean).

## 1. What exact merged-seat theorem was proved?

For finite J, actual-offset map seat and supplied prime-label sets Q, define

```text
W(r) = (J.filter (seat(j)=r)).biUnion Q
C(J,seat,Q) = ∑ r∈J.image seat, (W(r).card−1).
```

These are `mergedSeatWitness` and `mergedSeatCharge`. `mergedSeatWitness_subset_activeSupport` proves W(r)⊆actual support from realization of each Q(j). `mergedSeatCharge_le_supportExcess` assumes every indexed offset is an actual candidate and every Q(j) is an actual support subset, then proves C≤E. It has no injectivity assumption. `mergedSeatCharge_le_supportExcess_of_modEq` takes admissible active primes and point congruences instead. Existing uncovered/prime consumers are exposed as `uncovered_nonempty_of_merged_certificates` and `prime_squareCell_of_merged_certificates` with the explicit B2<A+C premise.

The two definitions describe supplied evidence; the actual candidate, incidence, excess and uncovered objects remain unchanged.

## 2. How does it relate to the old injective theorem?

`mergedSeatWitness_eq_of_injOn` proves W(seat(j))=Q(j) for j∈J when the actual seat map is injective. `mergedSeatCharge_eq_indexed_of_injOn` proves C=∑j∈J(Q(j).card−1). Rewriting the new charge bound with this equality gives009's indexed bound.

The naive extension without injectivity is false. At anchor8, two indices both carry{3,5} at actual seat11. Index charge is2, merged charge is1, and actual E8=1. The regression establishes the last equality structurally: B2(8)=5 and four explicitly covered seats give E≤1 through the exact ledger; the merged certificate gives E≥1. It does not evaluate whole-shell incidence/excess. This preserves a genuine counterexample, not just a collision of labels.

## 3. Can shared-seat witnesses be merged without double counting?

Yes. Labels are Finsets and are unioned before cardinality. For nonempty P,Q, the neutral theorem `union_excess_add_inter_card` proves

```text
(|P∪Q|−1) + |P∩Q| = (|P|−1) + (|Q|−1) + 1.
```

Disjoint nonempty witnesses gain one unit over their separate local costs; intersection cardinality1 preserves those costs; intersection≥2 loses intersection-cardinality−1 units relative to summing the two indices. The union can still have greater charge than either single witness. Identical pairs illustrate the loss2→1. Shared{3,5} and{3,7} give a useful three-label charge2.

`add_excess_le_union_excess_of_inter_card_le_one` handles empty sets as well. `two_family_charge_le_supportExcess` permits two actual finite seat families with fixed witness sets to add their counted costs when the witness intersection has cardinality≤1, even if the seat families intersect.

These three quantities are distinct: index charge counts supplied family records; merged charge counts witness unions at actual seats; E is the full existing support-excess sum. Only the proved merged bound, or a specifically proved overlap-controlled sum, is used as evidence for E.

## 4. Are58 and68 solved structurally?

Yes. The basis7 certificates give:

| n | A | B2 | D=B2−A+1 | Merged C | C−D | Uncovered lower bound |
| --- | --- | --- | --- | --- | --- | --- |
|58|56|63|8|15|7|8|
|68|64|70|7|16|9|10|

Named theorems prove primes in(3364,3481) and(4624,4761). These are variable-size finite seat families, not the previous three-seat ceiling. Every supplied seat and prime label is checked against production support; the structural B2 cap and exact deficit ledger finish the argument.

## 5. What mixed-anchor CRT theorem was proved?

For n=2ᵃpᵏ, prime p, k>0 and active Q, m=product(Q) is coprime to2p. Neutral `exists_support_one_offset_le_period` solves point≡0 modm and point≡1 mod2p, with a positive offset≤2pm. `candidate_of_two_prime_power_point_modEq_one` proves actual candidate membership from the point selector and the window bound: coprimality with2p implies coprimality with2ᵃpᵏ and oddness.

`exists_candidate_support_of_mixed_product_le` applies when pm≤n. This is a sufficient condition, not a necessary one. The theorem permits p=2 as well; it therefore includes the requested odd-prime class. The selector-to-candidate lemma itself needs no primality or k>0 hypothesis.

`mixed_anchor_period_family_charge_le_supportExcess` proves

```text
⌊n/(p·product(Q))⌋ · (Q.card−1) ≤ E(n).
```

Period2pm lifts preserve both equations and are distinct actual candidates. The generic positive-lift lemma counts the finite image exactly. At n320=2⁶·5,Q={3,7}, the generic theorem supplies charge3, and offsets101,311,521 with point≡1 mod10 are checked explicitly.

For the requested mixed checkpoints58,62,68,74,76,80,82,86,88,92,94,98,100, every active basis7 pair/triple has counted range0 under this conservative selector period. `mixed_short_period_budget_zero` checks their factor forms and the zero floor for every eligible subset. The successful small-shell certificates use actual short-window hits at other unit residues or at long-period residues; they do not follow from the one-period sufficient inequality pm≤n. This distinguishes a weak guaranteed period bound from nonexistence of actual candidates.

## 6. How many of the25 survivors remain?

Basis7 is{3,5,7,11,13,17,19}. Remove anchor divisors, take every two- or three-prime subset, solve its support/parity residue, enumerate its positive lifts only in1..2n, retain actual candidates, and merge by actual offset. Basis10 adds only23,29,31 and is tested at97,107,127,211,503; it is not all primes below the anchor.

All actual family records, witness memberships, merged cardinalities, raw index sums and short-product subpool charges are kernel checked. The saturation theorem also checks that image seats are exactly controlled-basis multi-support candidate seats, and that their merged witnesses equal the restricted basis witnesses. Thus the charge calculation omits no productive label in the tested basis. It never enumerates the full active support of a shell.

Basis7 resolves24 survivors, leaving97 because C26<D30. Basis10 at97 gives C35 and resolves it. **The previous25 unresolved shells now have25 structural prime conclusions and zero remaining survivors under the adaptive two-basis audit.** This does not assert that the new pool meets demand outside these bounded shells.

| n | A | B2 | D | C7 | C7−D | Adaptive C |
| --- | --- | --- | --- | --- | --- | --- |
|47|46|54|9|18|9|18|
|53|52|60|9|13|4|13|
|58|56|63|8|15|7|15|
|59|58|71|14|19|5|19|
|61|60|74|15|18|3|18|
|62|60|69|10|18|8|18|
|64|64|75|12|18|6|18|
|67|66|80|15|18|3|18|
|68|64|70|7|16|9|16|
|71|70|85|16|20|4|20|
|73|72|89|18|21|3|21|
|74|72|90|19|23|4|23|
|76|72|87|16|21|5|21|
|79|78|94|17|23|6|23|
|80|64|72|9|11|2|11|
|82|80|99|20|20|0|20|
|83|82|107|26|27|1|27|
|86|84|103|20|23|3|23|
|88|80|94|15|19|4|19|
|89|88|111|24|26|2|26|
|92|88|108|21|27|6|27|
|94|92|115|24|25|1|25|
|97|96|125|30|26|-4|35|
|98|84|95|12|18|6|18|
|100|80|90|11|16|5|16|

The only failure at the first stage is a bounded-pool charge shortage. Every shell has actual candidate certificates, so none is classified as blocked on a missing candidate/window theorem. The two larger investigated anchors211 and503 remain below demand in both pools; they were not part of the original25.

## 7. How does merged charge compare with demand on prime checkpoints?

The following are exact finite values. A,B2 and charges are checked in Lean; C−D is signed report arithmetic. C7(short) uses only actual family records with product(Q)<n. It retains actual windowed seats and merges overlaps; independent family floor guarantees may not be added without an overlap theorem.

| Prime n | A | B2 | D | C7 | C7−D | C7(short) | C10 | C10−D |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
|47|46|54|9|18|9|10|—|—|
|53|52|60|9|13|4|9|—|—|
|59|58|71|14|19|5|14|—|—|
|61|60|74|15|18|3|14|—|—|
|67|66|80|15|18|3|16|—|—|
|71|70|85|16|20|4|17|—|—|
|73|72|89|18|21|3|17|—|—|
|79|78|94|17|23|6|20|—|—|
|83|82|107|26|27|1|22|—|—|
|89|88|111|24|26|2|23|—|—|
|97|96|125|30|26|-4|23|35|5|
|107|106|144|39|35|-4|33|42|3|
|127|126|170|45|38|-7|36|46|1|
|211|210|307|98|66|-32|64|81|-17|
|503|502|813|312|149|-163|149|188|-124|

Raw index sums can falsely suggest success. At n97 basis7 gives index46 against D30, but merged26 fails. At n211 basis10 gives index150 against D98, but merged81 fails. At n503 basis10 gives index348 against D312, but merged188 fails. These raw sums are never fed to the consumer.

The expanded-basis C/D ratios at97,107,127,211,503 are35/30,42/39,46/45,81/98,188/312. The last three decrease from above1 to about0.827 and0.603. Basis7's corresponding large-checkpoint ratios are38/45,66/98,149/312. This is a finite deterioration in the tested range, not an asymptotic theorem or a proof that every possible CRT provider fails. Adding more triples within the same basis cannot increase the merged labels once all pairs already saturate them.

The guaranteed floor prefixes are also checked separately. For each Q, retain the first T=⌊(n−1)/product(Q)⌋ parity-compatible lifts, equivalently those offsets≤2·product(Q)·T. `checkpoint_floor_charges_checked` verifies both their raw index cost and their correct merged charge. `checkpoint_floor_charge_le_excess` proves the merged prefix charge≤E through the checked candidate/support conditions. The independent floors are not added into E without merging.

| Prime n | Raw floor7 | Merged floor7 | Merged floor10 | D |
| --- | --- | --- | --- | --- |
|47|8|8|—|9|
|53|9|8|—|9|
|59|11|11|—|14|
|61|12|12|—|15|
|67|15|14|—|15|
|71|16|14|—|16|
|73|16|15|—|18|
|79|19|19|—|17|
|83|19|19|—|26|
|89|21|20|—|24|
|97|24|21|24|30|
|107|31|26|29|39|
|127|37|32|35|45|
|211|75|58|69|98|
|503|208|140|174|312|

Of the mandatory prime checkpoints, only79 meets demand with the basis7 guaranteed floor prefixes. Neither basis10 prefix meets demand at97,107,127,211,503. The full finite certificates at97/107/127 therefore use additional actual window hits, not just the old floor guarantee. The mixed-anchor selector likewise has zero pair/triple guaranteed floors at the13 small mixed checkpoints even though their actual certificates succeed.

## 8. Is there an exact reusable scaling lower bound?

Yes. For every prime n>7, `exists_prime_anchor_period_support_family` exposes the actual family seat sets of sizes⌊(n−1)/15⌋ for{3,5} and⌊(n−1)/21⌋ for{3,7}. Their witnesses share exactly one prime. The two-family theorem rigorously controls collisions, proving

```text
⌊(n−1)/15⌋ + ⌊(n−1)/21⌋ ≤ E(n).
12(n−1) ≤ 105·E(n) + 198.
```

The second statement is `prime_star_pair_linear_charge`, derived from exact remainder bounds below15 and21. It is equivalently a rational linear lower bound E≥(4/35)(n−1)−66/35. No estimate of prime distribution appears. At107 these two families guarantee12, improving009's single-triple guarantee2, but still below demand39. This is a proved overlap-controlled fixed-pool scaling result, not a uniform demand comparison.

## 9. Does merged CRT remain a credible uniform route?

Merged CRT is useful for certificate generation: it solves all25 previous hard finite shells and the extra prime anchors107/127, and two overlapping families supply a rigorous linear lower bound. The two tested fixed bases do not track demand at211/503. The data support continuing CRT as one provider while requiring basis growth or a supplementary charge source; they do not support a uniform theorem for either fixed basis.

The guaranteed floor-prefix pools are weaker still. Endpoint remainder hits and larger-period residues materially contribute to the finite successes. A future uniform provider has to control that contribution or supply enough additional labels; merely summing more floor formulas is insufficient and can overcount.

The audit does not prove how D grows for arbitrary n. In particular, it would be unjustified to promote the decreasing sampled ratios to a universal growth obstruction. The correct negative finding is the four explicit211/503 fixed-pool failures and the shared-seat overcount counterexample. There is no missing merge/mixed candidate bridge left in the implemented scope.

## 10. What exact theorem is missing?

One concrete next provider would select a controlled active-prime basis B(n), then take the finite actual candidate hits of its two-prime subsets. Let J(n,B) contain all(r,Q) with Q⊆B, |Q|=2, 0<r≤2n, Coprime nr, odd n²+r, and product(Q)∣n²+r. The needed quantitative statement is

```text
∀ n>0 with A(n)≤B2(n), ∃ B⊆activePrimes(n),
  B2(n)−A(n)+1 ≤ mergedSeatCharge J(n,B) Prod.fst Prod.snd.
```

It requires an actual construction and a proved uniform lower estimate, not a certificate record containing the desired inequality as a field. A prescribed finite constant-size basis is not justified by the checked data. Restricting J to guaranteed short-period floors loses long-period hits that materially help the finite results. An alternative exact target is a proved independent lower bound for additional distinct active labels at already witnessed seats, combined through witness union; its total must cover the remaining demand deficit.

The existing B2=B limitation on2ᵃpᵏ anchors still rules out gains from merely adding more two-anchor-prime exclusions in that class. Sharper incidence bounds for applicable other classes and independently proved evidence for several distinct active prime factors remain possible supplements, but neither is claimed here. Repeated powers of one prime do not add distinct support labels to the existing excess.

## Next developments proposed

1. Test a bounded hierarchy of prime bases with certificates and saturation checks, reporting the smallest tested basis meeting demand. Target the current211 deficit17 and503 deficit124 for basis10; do not label a larger-pool discovery a uniform result.
2. Prove a witness-union incremental-charge API for an existing nonempty witness and genuinely new labels. This would make direct factorization-multiplicity supplements countable without replacing CRT or double-counting labels.
3. Generalize the mixed point selector from1 to all units modulo2p. Different unit residues separate actual seats modulo2p, so their families can be aggregated with a proved separation argument. Exact endpoint hits still matter when every conservative floor is0.
4. Seek a uniform distribution/realization bound for productive long-period pair hits with an adaptively growing basis. The current exact fixed-family linear theorem has no comparison to arbitrary D(n); adding that missing estimate is the substantial number-theoretic step.

Outcome B is chosen for the scaling question despite the complete bounded survivor reduction: the merge/mixed machinery is proved and useful, but the larger checked demands exceed both fixed-pool charges.

Outcome B — MERGED CRT FORMALIZED, LIMITED SCALING
