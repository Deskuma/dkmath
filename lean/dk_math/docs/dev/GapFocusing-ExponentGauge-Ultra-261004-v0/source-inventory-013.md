# Source inventory 013

The following live sources were inspected before adding moment abstractions.

|Source|Exact reusable declarations / decision|
|---|---|
|ParitySafeCanonicalRootTail|`canonicalRoughCandidates`, `canonicalRootTail_card_eq_rough_support_sum`, `activeSupport_prod_dvd_point`, `rough_support_pow_le_point`; retain existing carriers and erasure semantics.|
|ParitySafeCanonicalRoughCount|`mem_uncovered_iff_no_activeSupport`, `roughWave_sum_eq_support_sum`, `roughWave_sum_eq_covered_add_tail`; promote the private empty-class argument as one set equality.|
|ParitySafePrimeAnchorCap|`sqrtCutoff_power_four_gt`, `sqrtCutoff_support_card_le_three`; all-anchor combinatorics do not need prime cap exactness.|
|PairOverlap|`squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity`, `card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus`; reuse counting method, not old full candidate carrier.|
|Internal.PairCombinatorics|`upperPairs`, `card_upperPairs_eq_choose`; reused unchanged.|
|ParitySafeTripleProductGate|`paritySafeTripleGateTriples`, `paritySafeCanonicalResidualTripleIncidence_packet`, `paritySafeCanonicalResidualTripleIncidence_mem_productWave`, `paritySafeTripleProductWaveBudget_eq_div_add_carry`, `paritySafeTripleGateFar_wave_card_le_one`; these use root-selected erased quotient support and a cubic gate.|
|ParitySafeFarProductWaveRoughCofactor|`paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor`, `paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector`, `paritySafeFarProductWaveRoughOffsets_card_le_one`, `paritySafeFarProductWaveRough_primeFactor_ge_key`; old roughness is below the key root and on its cofactor, not arbitrary sqrt cutoff.|
|ParitySafeReducedResidue|`mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`, `activePrime_reducedResidue_packet`, `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval`; needed coprimality and prime-divisor activation, no duplicate normalization.|
|ParitySafeMobiusOddCorrection|`paritySafeOddMultipleFloorDelta`, `paritySafeActiveWave_card_eq_oddRaw_add_correction`, `paritySafeOddMobiusCorrection_nonpos`; signed correction is left outside the Nat moment API.|
|Wave|`mem_squareWaveOffsets`, `card_squareWaveOffsets_eq_div_add_carry`, `squareWaveCarry_le_one`, `card_squareWaveOffsets_le_one_of_two_mul_lt_modulus`; raw wave subset maps proved before occupancy consumption.|
|ParitySafeCanonicalRootCharge|`paritySafeProductWave_card_eq_count`, `primeAnchorProductWaveCount`; pair/triple prime-anchor bounds retain parity and anchor exclusion.|
|Mathlib Finset.Card|`Finset.card_eq_three`, `Finset.card_le_card`; neutral ordered-triple bounded cardinal proof.|
|Mathlib Finset.Powerset|`Finset.mem_powersetCard`, `Finset.card_powersetCard`; audited, but a powerset abstraction is unnecessary for k<=3.|
|Mathlib finite sums|`Finset.sum_product_right'`, `Finset.sum_product'`, `Finset.sum_boole`; explicit function and Nat annotations avoid elaboration expansion.|
|Mathlib Nat.Sqrt / Nat.Prime.Defs|`Nat.succ_le_succ_sqrt'`, `Nat.sqrt_le_self`, `Nat.exists_prime_and_dvd`, `Nat.minFac_prime`, `Nat.minFac_sq_le_self`; quotient classification needs no factorization evaluation.|

## Carrier boundaries and optional old machinery

The new unordered triple carrier contains every actual p<q<s support triple on the sqrt-rough carrier. The old residual incidence contains two erased quotient labels together with an implicitly selected canonical root. They are not declared equal. The proved exact maps are to raw square product waves and to candidate product waves; those maps suffice for period, carry, prime-anchor floor, and exact product counting.

For a new triple-seat hit, exact factorization makes its product cofactor1, so the old cofactor roughness conditions would be immediate after a separate cubic-gate and canonical-ownership adapter. No old capacity is consumed without such an adapter. No extra graph/hypergraph or new E/I ledger was introduced.

## Additional parity refinement

Existing `paritySafeActiveWave_same_wave_quotient_rigidity` confirms the even separation principle for one prime label. The new neutral-in-modulus candidate theorem uses `Nat.Odd.sub_odd`, `Nat.dvd_sub` and `Nat.Coprime.mul_dvd_of_dvd_of_dvd` to extend that principle to product moduli, then maps the actual rough pair carrier by its proved candidate filter equality.
