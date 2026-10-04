# Instruction 009 — adaptive certificates and windowed CRT seats

Both mandatory three-seat certificates are proved using actual active-support subsets. The bounded three-seat budget solves five of the previous30 unresolved shells, leaving25. A reusable CRT module proves congruence transport, parity-adjusted window existence, indexed distinct-seat aggregation, and a counted prime-anchor family. The family supplies excess on an infinite arithmetic class; its charge is not proved to meet every shell's demand.

All new production results are exported through `DkMath.NumberTheory.Legendre`. Mandatory and bounded calibrations remain in `DkMathTest`. The original incidence/excess ledger and008 finite witness aggregation are reused. No production definition of the required charge is added.

Evidence: [source inventory](source-inventory-009.md), [findings](findings-009.md), [validation](validation-009.md), [CRT production module](../../../DkMath/NumberTheory/Legendre/ParitySafeCRTSeat.lean), [mandatory certificates](../../../DkMathTest/NumberTheory/LegendreAdaptiveCertificate.lean), [CRT regressions](../../../DkMathTest/NumberTheory/LegendreCRTSeat.lean), [classification proofs](../../../DkMathTest/NumberTheory/LegendreAdaptiveClassification.lean).

## 1. Are the proposed41/91 certificates valid in production support?

Yes. Each listed offset is an actual parity-safe candidate. Each specified witness belongs to `paritySafeActiveSupport`, checked through primehood, q≤n, q≠2, q∤n and q∣n²+r. No full active-support enumeration is used.

| n | Actual seats and witness sets | Total charge |
| --- | --- | --- |
|41|2:{3,11,17};24:{5,11,31};44:{3,5,23}|6|
|91|38:{3,47,59};44:{3,5,37};68:{3,11,23}|6|

`sum_witness_support_excess_le_supportExcess` already accepts arbitrary `R : Finset ℕ` and `P : ℕ → Finset ℕ`; its008 implementation is reused directly.

## 2. What excess and prime conclusions result?

Writing E for the existing support excess, A for candidate cardinality, B2 for the two-prime upper cap, and U for uncovered cardinality:

| n | B2 | A | Certified E | Certified U | Prime conclusion |
| --- | --- | --- | --- | --- | --- |
|41|44|40|E≥6|U≥2|∃p prime,1681<p<1764|
|91|76|72|E≥6|U≥2|∃p prime,8281<p<8464|

The structural cap and exact deficit ledger supply U≥A+6−B2. Whole-shell incidence and whole-shell excess are not evaluated. The finite cap/candidate values and witness memberships are kernel checked.

## 3. Which theorem transports CRT congruences to support?

`activeSupport_contains_of_point_modEq` takes Q⊆`squareAnchorOddActivePrimes n` and ∀q∈Q, `Nat.ModEq q (n^2+r) 0`, and proves Q⊆`paritySafeActiveSupport n r`. Support transport itself needs no candidate premise. `activeSupport_contains_of_product_dvd` supplies the same conclusion from product(Q)∣n²+r. `local_excess_ge_of_point_modEq` gives the corresponding local cardinality charge with explicit candidate membership.

The equations are homogeneous on the shell point. Product divisibility supplies every q equation; the construction combines this product modulus with modulus2 using `Nat.chineseRemainder`. Natural-number residues use `m−(n² % m)`, rather than interpreting truncated `0−n²` as a negative residue.

## 4. What makes a CRT offset an actual candidate?

The exact conditions are 0<r≤2n, `Nat.Coprime n r`, and `Odd (n²+r)`. They are packaged by `candidate_of_window_coprime_odd`. Active-prime side conditions alone do not prove anchor coprimality or parity.

For prime n, `coprime_prime_anchor_of_strict_window_odd` proves coprimality from 0<r<2n and odd n²+r: an anchor multiple in the strict window would be r=n, whose point n²+n is even. The strict upper bound matters.

## 5. Is there a useful product-based short-window theorem?

Yes, with separate conclusions:

- `exists_pos_modEq_le_window`: m>0 and m≤W give a positive representative≤W of any residue modulo m. Residue0 uses endpoint m.
- `exists_parity_offset_le_two_mul_period`: m>0 and Coprime m2 give 0<r≤2m with m∣n²+r and odd n²+r.
- `exists_windowed_odd_support_of_product_le`: active Q and product(Q)≤n place such an odd supported point in1..2n. Coprimality remains unproved for a general anchor.
- `exists_candidate_support_of_prime_product_lt`: prime n and product(Q)<n produce an actual candidate carrying Q.

Kernel-checked counterexamples preserve the failed stronger claims. At n11,Q={3,7}, period21 fits22 but the only raw hit has offset5 and wrong point parity. At n6,Q={5}, parity period10 fits12 and its odd hit is offset9, but gcd(6,9)>1, so no candidate carries that witness. The zero-residue regression also shows why offset0 cannot be used.

The criterion is sufficient, not necessary. Mandatory41/91 witness products are respectively561,1705,345 and8319,555,759, exceeding their shell windows82 and182. Their actual short-window hits are proved separately. In2..100, every three-distinct-odd-prime product is at least105, so the prime-anchor short-product triple provider does not account for these finite successes.

## 6. Can multiple distinct seats supply a proved charge?

Yes. `sum_indexed_modEq_charge_le_supportExcess` requires injectivity of the actual seat map over a finite index set. Its uncovered and square-cell prime consumers apply when the summed charge beats the cap deficit. `seat_ne_of_distinct_modEq_classes` supplies one sufficient separation mechanism. Distinct witness sets alone are insufficient: the regression realizes both{3,5} and{3,23} at the same actual seat44 of shell41.

For prime n and active Q, let m=product(Q), T=⌊(n−1)/m⌋. A parity CRT base0<r≤2m yields actual distinct candidate seats r+2m·j for0≤j<T. The theorem `prime_anchor_period_family_charge_le_supportExcess` proves

```text
⌊(n−1)/product(Q)⌋ · (Q.card−1) ≤ E(n).
```

Each seat is positive and strictly below2n; oddness and product divisibility persist under the lift; prime-anchor coprimality follows as above. A long period can give T=0, supplying no positive charge. At prime211,Q={3,5,7}, offsets104 and314 are checked actual candidates, and the generic family proves E211≥4.

## 7. How many previous unresolved shells are solved?

All30 previous Class2 shells in2..100 are revisited with up to3 distinct seats and up to3 witnesses per seat. Every claimed dataset property and resulting conclusion is kernel checked. The Python generator is certificate discovery, not proof.

| Class | Shells | Count |
| --- | --- | --- |
|Solved with charge5|41,43,56,91|4|
|Solved with charge6|44|1|
|Still unresolved under this budget|table below|25|

For charge5 successes, the diagnostic certificate truncates one triple to a two-prime subset; the separate mandatory41/91 proofs retain all three triples and charge6. The other previous69 successful shells are unchanged; combining the checkpoints gives74 successful shells and25 unresolved among2..100.

## 8. Which shells survive and why?

D=B2−A+1 is a report quantity. All survivors have B2≥A and three actual triple-witness seats, hence certified E≥6. In every row D>6, and the kernel-checked `diagnostic_survivor_budget_obstruction` proves every e≤6 fails B2<A+e. Failure is the stated charge ceiling, not an absence of suitable multi-support seats. Larger certificates and other caps remain open.

| n | B2 | A | D | Best found charge | Arithmetic type |
| --- | --- | --- | --- | --- | --- |
|47|54|46|9|6|prime|
|53|60|52|9|6|prime|
|58|63|56|8|6|2·29|
|59|71|58|14|6|prime|
|61|74|60|15|6|prime|
|62|69|60|10|6|2·31|
|64|75|64|12|6|2⁶|
|67|80|66|15|6|prime|
|68|70|64|7|6|2²·17|
|71|85|70|16|6|prime|
|73|89|72|18|6|prime|
|74|90|72|19|6|2·37|
|76|87|72|16|6|2²·19|
|79|94|78|17|6|prime|
|80|72|64|9|6|2⁴·5|
|82|99|80|20|6|2·41|
|83|107|82|26|6|prime|
|86|103|84|20|6|2·43|
|88|94|80|15|6|2³·11|
|89|111|88|24|6|prime|
|92|108|88|21|6|2²·23|
|94|115|92|24|6|2·47|
|97|125|96|30|6|prime|
|98|95|84|12|6|2·7²|
|100|90|80|11|6|2²·5²|

There are11 prime anchors,13 mixed anchors2ᵃpᵏ, and one power-of-two anchor. Their at-most-one-distinct-odd-factor property is kernel checked, placing them within008's general B2=B limitation. More two-prime anchor exclusion alone cannot improve their cap. The survivor table is generated from [checked diagnostic data](logs/classification-009.json); [summary](logs/classification-summary-009.txt).

## 9. Is there an infinite arithmetic-class provider?

Yes: `supportExcess_ge_two_of_prime_gt_105` proves E(n)≥2 for every prime n>105, using Q={3,5,7}. The counted-family theorem strengthens this to2⌊(n−1)/105⌋. These actual candidate certificates apply to an infinite class of prime anchors. `prime_squareCell_of_prime_period_family_gap` gives a prime only under the explicit remaining demand inequality.

This is not a uniform prime-existence provider. At n107 the kernel checks B2=144,A=106,D=39, whereas the fixed-Q family supplies only2. The regression states failure of the charge2 criterion; it does not assert E107=2. Among three-prime short products at107,105 is the only possible one, so that restricted construction alone cannot meet this demand.

## 10. What precise provider is still missing?

After the existing zero-excess cases, the missing statement can be expressed without changing production definitions:

```text
∀ n>0 with A(n)≤B2(n), ∃ R : Finset ℕ, ∃ P : ℕ→Finset ℕ,
  R ⊆ actualCandidates(n) ∧
  (∀ r∈R, P(r) ⊆ activePrimes(n)) ∧
  (∀ r∈R, ∀ q∈P(r), Nat.ModEq q (n²+r) 0) ∧
  B2(n)−A(n)+1 ≤ ∑ r∈R, (P(r).card−1).
```

This would feed the proved adaptive consumer. It is a sufficient uniform provider requirement for this method, not a proved theorem or a claim that all possible proof methods require it. The current obstacle is quantitative charge on actual distinct short-window seats: admissible primes and unrestricted CRT solvability do not ensure parity/coprimality-compatible hits or a summed charge meeting demand. Same-modulus lifts solve distinctness within one family; overlaps between different families require merging witnesses at actual seats or a new separation argument.

## Next developments proposed

1. Extend bounded discovery by the actual demand, retaining explicit certificates: first test four-seat budgets on68(D7) and58(D8), then larger budgets for97(D30). No such certificates are claimed here. Allow two-prime and four-prime subsets and merge overlapping witness families by actual seat before counting charge.
2. Prove a reusable union-of-families charge bound that handles shared seats through witness unions. Counting labels from different CRT systems would otherwise double-count excess.
3. For mixed anchors n=2ᵃpᵏ with k>0, investigate CRT on point residues0 modulo m and1 modulo2p. Coprimality of these moduli follows when Q excludes2,p; the proposed parity/coprimality period is2pm and the sufficient window condition pm≤n. This route has not been implemented or shown to meet demand.
4. Compare demand growth against counted charges before proposing a uniform short-product family conjecture. The checked107 example already excludes the restricted one-triple short-period budget as a uniform solution.

The completed scope is structural finite certificates, reusable CRT/candidate bridges, and a quantitative infinite-class excess provider. A uniform Legendre theorem remains unproved.

Outcome A — ADAPTIVE CERTIFICATE PROVIDER ADVANCES
