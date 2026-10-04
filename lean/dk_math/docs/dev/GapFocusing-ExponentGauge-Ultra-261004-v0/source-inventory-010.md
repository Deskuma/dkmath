# Instruction 010 source inventory

Baseline `cd04ef580`,009 implementation `320b42522`; initial checkout clean. [Lean inventory](../../../DkMathTest/NumberTheory/LegendreMergedCRTInventory.lean), [exact source types](logs/source-inventory-010.txt).

| Required source | Existing interfaces audited before extension |
| --- | --- |
|`ParitySafeCRTSeat`|`activeSupport_contains_of_point_modEq`, `candidate_of_window_coprime_odd`, `sum_indexed_modEq_charge_le_supportExcess`, `prime_anchor_period_family_charge_le_supportExcess`, `exists_candidate_support_of_prime_product_lt`; injective aggregation and counted one-family provider|
|`ParitySafeExcessCertificate`|`sum_witness_support_excess_le_supportExcess`, `paritySafeUncovered_nonempty_of_local_witnesses`, `exists_prime_squareCell_of_local_witnesses`; original finite witness/cap deficit consumers|
|`ParitySafeIncidenceUpper`|`paritySafeIncidenceCount_le_twoPrimeUpper`, `paritySafeTwoPrimeIncidenceUpper_eq_upper_two_pow_mul_prime_pow`; actual B2 cap and prime-power limitation|
|`ParitySafeIncidenceBalance`|`mem_paritySafeActiveSupport_iff_dvd`, `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence`; actual support and exact ledger|
|`ParitySafeReducedResidue`|`mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`, `activePrime_reducedResidue_packet`; actual point coprimality characterization|
|`ParitySafeBlockLocalization`|`block_incidence_add_uncovered_eq_candidate_add_supportExcess`; original ledger remains unchanged|

Mathlib: `Finset.mem_biUnion`, `card_union_add_card_inter`, `sum_image`, `sum_union_inter`, `sum_ite_mem`, `Nat.chineseRemainder`, `Nat.ModEq.add_left`, `Nat.ModEq.of_dvd`, `Nat.ModEq.dvd_iff`, `Nat.coprime_of_mul_modEq_one`, `Nat.Coprime.pow_left`, `Nat.coprime_mul_iff_left`, `Nat.Coprime.prod_left`, `Nat.mod_add_div`. There is no `Nat.ModEq.coprime_iff` in this checkout; the point-one proof uses the checked `coprime_of_mul_modEq_one` instead.

New production homes are [ParitySafeMergedCRT](../../../DkMath/NumberTheory/Legendre/ParitySafeMergedCRT.lean) for substantial noninjective union/charge mathematics and consumers, and [ParitySafeMixedCRT](../../../DkMath/NumberTheory/Legendre/ParitySafeMixedCRT.lean) for candidate-aware period construction, mixed anchors and controlled two-family scaling. Neutral union/cardinality and period arithmetic are in `DkMath.NumberTheory`; application objects are in `DkMath.NumberTheory.Legendre`. Both are exported by the Legendre facade.009 and the original incidence/excess definitions are retained.

The two new public definitions describe supplied witness unions and their charge, not a new actual incidence/excess object. Diagnostic bases, family tables and discovery remain in `DkMathTest` and the bounded checks directory.
