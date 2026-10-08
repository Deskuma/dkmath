# Instruction012 source inventory

The clean live checkout and the completed011 checkpoint were inspected before
implementation. The existing E incidence is reused; no replacement excess
ledger is introduced. Source probes are kept in
[DkMathTest inventory](../../../DkMathTest/NumberTheory/LegendreCanonicalTailInventory.lean)
and [its compiler output](evidence/MANIFEST.md#log-e274f086078db255).

|Audited module|Exact existing declarations used or compared|Decision|
|---|---|---|
|`ParitySafeCanonicalRootFiber`|`mem_canonicalIncidence_iff`, `canonicalSupport_eq_iff_minimal`, `canonicalSupport_eq_iff_no_smaller`, `canonicalIncidence_root_lt`, `supportExcess_eq_sum_canonicalRootFiber`, `canonicalRootFiber_card_eq_sum_pairs`, `mem_canonicalRootPairOffsets_iff`|Filter the existing canonical incidence; retain root erasure and candidate parity/coprimality.|
|`ParitySafeCanonicalRootSieve`|`card_filter_two_exclusions`, `card_finite_exclusion_lower`, `canonicalRootSieveLower`, `canonicalRootSieveLower_le_fiber`, `sum_canonicalRootSieveLower_le_excess`, `activePrimes_coprime`, `productWave_filter_dvd`, `primeAnchor_small_roots`|Add only neutral three-exclusion IE; formally normalize the old root11 union provider for comparison.|
|`ParitySafeCanonicalRootCharge`|`primeAnchorProductWaveCount`, `paritySafeProductWave_card_eq_count`, `canonicalRootCharge3`, `canonicalRootCharge5`, `canonicalRootCharge7`, `canonicalSmallRootCharges_eq_fibers`, `canonicalSmallRootCharges_le_excess`|Reuse corrected candidate floor waves; append exact root11.|
|`ParitySafeIncidenceUpper`|`paritySafeTwoPrimeWaveUpper`, `paritySafeTwoPrimeIncidenceUpper`, `paritySafeActiveWave_card_le_twoPrimeWaveUpper`, `paritySafeIncidenceCount_le_twoPrimeUpper`, `paritySafeTwoPrimeWaveUpper_le_waveUpper`|Prove pointwise head+tail<=cap before distributing Nat subtraction. General cap slack remains explicit.|
|`ParitySafeReducedResidue`|`card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul`, `paritySafeActiveWaveOffsets_quotient_properties`, `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval`, `paritySafeIncidenceCount_eq_reducedQuotientInterval_sum`|Actual q-wave is exact reduced-quotient occupancy. No cap equality is assumed.|
|`ParitySafeFarProductWaveRoughCofactor`|`paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor`, `paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector`, `paritySafeCanonicalFarResidual_card_eq_roughProductWaveSelector_sum`, `paritySafeFarProductWaveRoughOffsets_card_le_one`|Existing far-product roughness uses a different carrier/key selector; do not identify its finite capacity with the complete root tail.|
|`ParitySafeNearFirstPrimeWaveCapacity`|`paritySafeTripleGateNearTriples_card_eq_sum_firstPrime_pairFibers`, `paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget`, `paritySafeNearFirstPrimeWaveBudget_eq_div_add_carry`|A near-triple budget is not a bound on all rough secondary incidence.|
|`PairOverlap`|`squarePrimePairOverlapCount_eq_sum_product_div_add_carry`, `squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar`|Unordered pair multiplicity is not canonical excess. The product-wave intersection equivalence is `squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product` in the imported overlap base.|
|`ParitySafeMobiusOddCorrection`|`card_filter_odd_dvd_Ioc_eq_paritySafeDelta`, `paritySafeActiveWave_card_eq_oddRaw_add_correction`, `paritySafeOddMobiusCorrection_nonpos`|Reuse exact odd-multiple floor deltas, with anchor exclusion.|
|`ParitySafeIncidenceBalance` / production consumers|`mem_paritySafeActiveSupport_iff_dvd`, `mem_paritySafeCoveredCandidates`, `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence`, `paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card`, `paritySafeActiveSupport_subset_pointPrimeFactors`, `paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess`, `exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty`|Reuse C+E=I and C+U=A. The older `mem_paritySafeUncoveredCandidates_iff` states a covering predicate and needs n>0; add a direct support-empty membership normal form.|

Mathlib finite arithmetic was also inspected: `Finset.sum_tsub_distrib` requires
pointwise inequalities and works for Nat; `Finset.sum_sub_distrib` is a group
identity and cannot justify this Nat cancellation. Distinct support primes use
`Nat.prod_primeFactors_dvd`, `Finset.prod_dvd_prod_of_subset` and
`Finset.pow_card_le_prod`. No logarithms or analytic sieve estimates are needed.

The phase3 proposed bare rough-support object counts the canonical root as
well as non-root labels. The corrected tail characterization adds existence of
a smaller supported active label below q. A separate full rough wave is useful
for direct counting and is explicitly named as incidence, not tail.

The additional cap audit produced a scope-restricted result rather than a
general identification. `ParitySafePrimeAnchorCap` proves
`primeAnchorTwoPrimeWaveUpper_eq_count`, `primeAnchorTwoPrimeWaveUpper_eq_card`,
`primeAnchorTwoPrimeUpper_eq_incidence`,
`primeAnchorRemainingCap_eq_covered_tail`,
`primeAnchorRemainingCap_lt_iff_rough` and `primeAnchorHead_gap_iff_rough` for
prime n!=2. The singleton `Nat.Prime.primeFactors` identity supplies complete
anchor exclusion. General anchors retain the explicit B2-I slack.

The explicit cutoff audit also reuses `Nat.succ_le_succ_sqrt'` from Mathlib's
Nat sqrt source. Three additional production theorems prove the fourth-power
threshold, support.card<=3 and tail<=2*roughSeats at cutoff floor(sqrt n).
These require no prime-anchor hypothesis and make no demand-sufficiency claim.

Final diagnostic layout separates closed numeric proofs in
`LegendreCanonicalTailDiagnosticCounts` from production-object transports in
`LegendreCanonicalTailDiagnostics`, retaining the same public namespace and
declaration names. Actual E/tail values use rough-covered counts plus the
already checked exact rough-incidence floor sum; full-support E is not directly
evaluated as a numerical proof.
