# Source inventory 016

Live pre-extension audit. Existing modular/CRT framework is reused.

## DkMath.Gnomon.Algebra

- `oddGnomon` — `DkMath/Gnomon/Algebra.lean:31`
- `squareGnomonBand` — `DkMath/Gnomon/Algebra.lean:35`
- `petalMul` — `DkMath/Gnomon/Algebra.lean:39`
- `oddGnomon_zero` — `DkMath/Gnomon/Algebra.lean:42`
- `oddGnomon_succ` — `DkMath/Gnomon/Algebra.lean:45`
- `oddGnomon_pos` — `DkMath/Gnomon/Algebra.lean:50`
- `oddGnomon_odd` — `DkMath/Gnomon/Algebra.lean:54`
- `oddGnomon_injective` — `DkMath/Gnomon/Algebra.lean:58`
- `oddGnomon_eq_one_iff` — `DkMath/Gnomon/Algebra.lean:64`
- `petalMul_zero_left` — `DkMath/Gnomon/Algebra.lean:74`
- `petalMul_zero_right` — `DkMath/Gnomon/Algebra.lean:78`
- `petalMul_comm` — `DkMath/Gnomon/Algebra.lean:82`
- `petalMul_assoc` — `DkMath/Gnomon/Algebra.lean:87`
- `oddGnomon_petalMul` — `DkMath/Gnomon/Algebra.lean:92`
- `square_add_oddGnomon` — `DkMath/Gnomon/Algebra.lean:97`
- `square_add_squareGnomonBand` — `DkMath/Gnomon/Algebra.lean:102`
- `squareGnomonBand_zero` — `DkMath/Gnomon/Algebra.lean:107`
- `squareGnomonBand_unit` — `DkMath/Gnomon/Algebra.lean:111`
- `squareGnomonBand_zero_anchor` — `DkMath/Gnomon/Algebra.lean:115`
- `squareGnomonBand_add` — `DkMath/Gnomon/Algebra.lean:119`
- `squareGnomonBand_eq_sum_shifted_oddGnomon` — `DkMath/Gnomon/Algebra.lean:125`
- `sum_oddGnomon_eq_square` — `DkMath/Gnomon/Algebra.lean:143`
- `sum_odd_eq_square` — `DkMath/Gnomon/Algebra.lean:152`

## DkMath.NumberTheory.Legendre.Basic

- `SquareCell` — `DkMath/NumberTheory/Legendre/Basic.lean:32`
- `SquareOffset` — `DkMath/NumberTheory/Legendre/Basic.lean:36`
- `SquareOffsetForbiddenBy` — `DkMath/NumberTheory/Legendre/Basic.lean:40`
- `SquareOffsetCovered` — `DkMath/NumberTheory/Legendre/Basic.lean:44`
- `squareOffsetCovered_iff_exists_prime_dvd` — `DkMath/NumberTheory/Legendre/Basic.lean:48`
- `supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` — `DkMath/NumberTheory/Legendre/Basic.lean:60`
- `squareAnchorForbiddenResidue` — `DkMath/NumberTheory/Legendre/Basic.lean:75`
- `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue` — `DkMath/NumberTheory/Legendre/Basic.lean:79`
- `squareOffsetPrimeSupport` — `DkMath/NumberTheory/Legendre/Basic.lean:114`
- `mem_squareOffsetPrimeSupport` — `DkMath/NumberTheory/Legendre/Basic.lean:119`
- `squareOffsetCovered_iff_primeSupport_nonempty` — `DkMath/NumberTheory/Legendre/Basic.lean:128`
- `squareOffsetCovered_iff_primeSupport_card_pos` — `DkMath/NumberTheory/Legendre/Basic.lean:141`
- `squareOffsetForbiddenBy_pair_iff_product_dvd` — `DkMath/NumberTheory/Legendre/Basic.lean:147`
- `squareOffsetForbiddenBy_pair_iff_product_phase` — `DkMath/NumberTheory/Legendre/Basic.lean:159`
- `SquareOffsetOverlap` — `DkMath/NumberTheory/Legendre/Basic.lean:182`
- `squareOffsetOverlap_iff_exists_distinct_support` — `DkMath/NumberTheory/Legendre/Basic.lean:186`
- `squareCell_iff_exists_squareOffset` — `DkMath/NumberTheory/Legendre/Basic.lean:215`
- `LegendreConjecture` — `DkMath/NumberTheory/Legendre/Basic.lean:238`
- `SquareAnchoredSupportEscape` — `DkMath/NumberTheory/Legendre/Basic.lean:245`
- `squareOffsets` — `DkMath/NumberTheory/Legendre/Basic.lean:251`
- `mem_squareOffsets` — `DkMath/NumberTheory/Legendre/Basic.lean:255`
- `card_squareOffsets` — `DkMath/NumberTheory/Legendre/Basic.lean:261`

## DkMath.NumberTheory.Legendre.Wave

- `squareWaveOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:32`
- `mem_squareWaveOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:37`
- `squarePrimeWaveOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:46`
- `mem_squarePrimeWaveOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:50`
- `eq_of_mem_squareWaveOffsets_of_two_mul_lt_modulus` — `DkMath/NumberTheory/Legendre/Wave.lean:57`
- `card_squareWaveOffsets_le_one_of_two_mul_lt_modulus` — `DkMath/NumberTheory/Legendre/Wave.lean:80`
- `card_squareWaveOffsets_eq_div_sub_div` — `DkMath/NumberTheory/Legendre/Wave.lean:95`
- `squareWaveCarry` — `DkMath/NumberTheory/Legendre/Wave.lean:161`
- `squareWaveCarry_le_one` — `DkMath/NumberTheory/Legendre/Wave.lean:165`
- `squareWaveCarry_eq_one_iff` — `DkMath/NumberTheory/Legendre/Wave.lean:179`
- `squareWaveCarry_eq_zero_iff` — `DkMath/NumberTheory/Legendre/Wave.lean:198`
- `card_squareWaveOffsets_eq_div_add_carry` — `DkMath/NumberTheory/Legendre/Wave.lean:218`
- `squareWaveCarry_eq_zero_of_dvd_anchor` — `DkMath/NumberTheory/Legendre/Wave.lean:242`
- `card_squareWaveOffsets_eq_div_of_dvd_anchor` — `DkMath/NumberTheory/Legendre/Wave.lean:252`
- `card_squarePrimeWaveOffsets_eq_div_add_carry` — `DkMath/NumberTheory/Legendre/Wave.lean:262`
- `card_squarePrimeWaveOffsets_eq_div_of_dvd_anchor` — `DkMath/NumberTheory/Legendre/Wave.lean:270`
- `card_squarePrimeWaveOffsets_eq_div_sub_div` — `DkMath/NumberTheory/Legendre/Wave.lean:278`
- `div_le_card_squareWaveOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:287`
- `card_squareWaveOffsets_le_div_add_one` — `DkMath/NumberTheory/Legendre/Wave.lean:296`
- `two_le_card_squarePrimeWaveOffsets_of_mem` — `DkMath/NumberTheory/Legendre/Wave.lean:305`
- `squarePrimePairOverlapOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:317`
- `mem_squarePrimePairOverlapOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:323`
- `squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product` — `DkMath/NumberTheory/Legendre/Wave.lean:331`
- `card_squarePrimePairOverlapOffsets_eq_div_sub_div` — `DkMath/NumberTheory/Legendre/Wave.lean:342`
- `card_squarePrimePairOverlapOffsets_le_one_of_two_mul_lt_product` — `DkMath/NumberTheory/Legendre/Wave.lean:353`
- `coveredSquareOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:365`
- `escapingSquareOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:370`
- `mem_coveredSquareOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:375`
- `mem_escapingSquareOffsets` — `DkMath/NumberTheory/Legendre/Wave.lean:383`
- `mem_escapingSquareOffsets_iff_supportDisjointFrom` — `DkMath/NumberTheory/Legendre/Wave.lean:391`
- `SquareOffsetsFullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:400`
- `squareCoverIncidenceCount` — `DkMath/NumberTheory/Legendre/Wave.lean:404`
- `squareCoverBaselineIncidence` — `DkMath/NumberTheory/Legendre/Wave.lean:408`
- `squareAnchorCarryCount` — `DkMath/NumberTheory/Legendre/Wave.lean:412`
- `card_squareOffsets_le_squareCoverIncidenceCount_of_fullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:416`
- `two_mul_le_squareCoverIncidenceCount_of_fullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:432`
- `squareCoverIncidenceCount_eq_sum_primeWave_cards` — `DkMath/NumberTheory/Legendre/Wave.lean:439`
- `squareCoverIncidenceCount_eq_baseline_add_carry` — `DkMath/NumberTheory/Legendre/Wave.lean:461`
- `squareAnchorCarryCount_le_card_primeScalesUpTo` — `DkMath/NumberTheory/Legendre/Wave.lean:474`
- `squareCoverIncidenceCount_eq_sum_div_sub_div` — `DkMath/NumberTheory/Legendre/Wave.lean:486`
- `two_mul_le_sum_div_sub_div_of_fullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:498`
- `squareCoverOverlapExcess` — `DkMath/NumberTheory/Legendre/Wave.lean:507`
- `squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:512`
- `squareCoverBaselineIncidence_add_squareAnchorCarryCount_eq_two_mul_add_overlapExcess_of_fullyCovered` — `DkMath/NumberTheory/Legendre/Wave.lean:538`

## DkMath.NumberTheory.Legendre.Frontier

- `squareOffsetsFullyCovered_iff_coveredSquareOffsets_eq` — `DkMath/NumberTheory/Legendre/Frontier.lean:25`
- `not_squareOffsetsFullyCovered_iff_escaping_nonempty` — `DkMath/NumberTheory/Legendre/Frontier.lean:45`
- `squareAnchoredSupportEscape_iff_not_fully_covered` — `DkMath/NumberTheory/Legendre/Frontier.lean:63`
- `squareAnchoredSupportEscape_iff_raw` — `DkMath/NumberTheory/Legendre/Frontier.lean:82`
- `prime_of_squareAnchoredSupportEscape` — `DkMath/NumberTheory/Legendre/Frontier.lean:96`
- `legendreConjecture_of_squareAnchoredSupportEscape` — `DkMath/NumberTheory/Legendre/Frontier.lean:111`
- `is` — `DkMath/NumberTheory/Legendre/Frontier.lean:124`
- `legendreConjecture_iff_squareAnchoredSupportEscape` — `DkMath/NumberTheory/Legendre/Frontier.lean:126`
- `legendreConjecture_iff_squareOffsets_not_fully_covered` — `DkMath/NumberTheory/Legendre/Frontier.lean:149`

## DkMath.NumberTheory.Legendre.PrimorialWheelBridge

- `primeScalesUpTo_isFinitePrimeBasis` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:37`
- `primeScalesUpTo_nonempty_of_two_le` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:43`
- `squareOffsetCovered_iff_reservedByPrimeBasis` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:52`
- `not_squareOffsetCovered_iff_not_reservedByPrimeBasis` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:59`
- `not_squareOffsetCovered_iff_projection_survivor` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:68`
- `squareOffset_prime_iff_not_covered` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:86`
- `squareOffset_prime_iff_projection_survivor` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:109`
- `legendreConjecture_iff_projectedWheelEscape_from_two` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:126`
- `primorialWheelBridge_four_one` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:156`
- `primeScalesUpTo_one_empty_wheel_boundary` — `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:169`

## DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor

- `primeScalesUpTo_succ_eq` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:35`
- `SuccessorOldBasisReserved` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:68`
- `successorOldBasisReserved_iff_shiftedOffset` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:72`
- `squareOffset_succ_shiftedOffset_range` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:81`
- `squareOffsetCovered_succ_iff_old_or_threshold` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:91`
- `successorThresholdPrime_dvd_iff` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:124`
- `squareOffsetCovered_succ_iff_threshold` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:158`
- `squareOffsetCovered_succ_iff_old_of_not_prime` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:172`
- `successorProjectedSurvivor_iff_primeThreshold` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:180`
- `successorProjectedSurvivor_iff_composite` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:193`
- `squareOffsetsFullyCovered_succ_iff_primeThreshold` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:207`
- `squareOffsetsFullyCovered_succ_iff_composite` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:220`
- `successorThresholdRegression_four_ten` — `DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean:234`

## DkMath.NumberTheory.Legendre.GnomonSuccessor

- `card_squareOffsets_succ_add_two` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:31`
- `oddGnomon_succ_add_two` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:37`
- `successorThresholdOffsets` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:45`
- `successorThresholdOffsets_subset_squareOffsets_succ` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:49`
- `card_successorThresholdOffsets` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:63`
- `mem_successorThresholdOffsets_iff_threshold_dvd` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:69`
- `card_squareOffsets_succ_sdiff_threshold` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:77`
- `successorThresholdInsert` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:89`
- `successorThresholdInsert_mem_sdiff` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:93`
- `dvd_oddGnomon_of_dvd_adjacent_square_points` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:125`
- `oldPrime_not_common_sameOffset` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:138`
- `successorThresholdInsert_lower_additive_displacement` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:149`
- `successorThresholdInsert_upper_additive_displacement` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:161`
- `dvd_oddGnomon_of_dvd_reindexed_lower_common` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:169`
- `dvd_two_mul_succ_of_dvd_reindexed_upper_common` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:178`
- `primeScalesUpTo_31_eq_insert` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:190`
- `successorThresholdOffsets_30_eq` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:195`
- `card_squareOffsets_31_sdiff_threshold_30` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:199`
- `successor_reindex_30_6_mismatch` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:205`
- `successor_reindex_30_7_mismatch` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:220`
- `oldPrime_30_not_common_lower_reindex` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:235`
- `oldPrime_30_common_upper_reindex_dvd_62` — `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:251`

## DkMath.NumberTheory.Legendre.GnomonSupportTurnover

- `mem_reindexed_primeSupport_inter_lower_iff` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:27`
- `reindexed_primeSupport_inter_lower_eq_filter` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:57`
- `mem_reindexed_primeSupport_inter_upper_iff` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:70`
- `reindexed_primeSupport_inter_upper_eq_filter` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:100`
- `oldPrime_dvd_two_mul_succ_imp_eq_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:115`
- `oldPrime_dvd_two_mul_succ_iff_eq_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:131`
- `mem_reindexed_primeSupport_inter_upper_imp_eq_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:143`
- `reindexed_primeSupport_inter_upper_eq_filter_eq_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:157`
- `disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:180`
- `disjoint_reindexed_primeSupport_upper_of_prime_succ_of_not_dvd_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:200`
- `disjoint_reindexed_primeSupport_lower_30` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:219`
- `mem_reindexed_primeSupport_inter_upper_30_imp_eq_two` — `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:226`

## DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier

- `paritySafeResidualPairMass_le_lowCostCapacity_add_terminal_add_depthResidualCapacity` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:36`
- `two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:54`
- `paritySafeUncoveredCandidates_eq_empty_of_fullyCovered` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:70`
- `paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:85`
- `two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:103`
- `two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_fullCoverCapacity` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:121`
- `two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_reducedQuotient_fullCoverCapacity` — `DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean:139`

## DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus

- `sqrt_rough_three_factor_packet` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:16`
- `sqrtRepeatedProduct` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:56`
- `sqrtRoughRepeatedKeys` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:59`
- `sqrt_repeated_offset_packet` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:63`
- `sqrt_repeated_keys_offset_injective` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:87`
- `sqrt_repeated_pair_occupancy` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:134`
- `roughRepeatedSeats` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:159`
- `rough_double_eq_repeated_seats` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:162`
- `rough_double_card_eq_repeated` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:193`
- `sqrt_triple_offset_packet` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:198`
- `sqrt_triple_keys_offset_injective` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:207`
- `roughTripleProductSeats` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:221`
- `rough_triple_eq_product_seats` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:224`
- `rough_triple_card_eq_products` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:246`
- `sqrt_product_seats_pairwise_disjoint` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:252`
- `sqrt_product_seats_union` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:274`
- `sqrt_zero_point_prime` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:282`
- `sqrt_rough_point_factorization` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:296`
- `sqrt_rough_factorization_census` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:329`
- `sqrt_product_pairMoment` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:337`
- `sqrt_product_incidence` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:342`
- `sqrt_product_covered` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:349`
- `sqrt_uncovered_pos_iff_product_census` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:357`
- `prime_squareCell_of_sqrt_factorization_census` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:365`
- `prime_squareCell_of_cross_fiber_budget` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean:375`

## DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation

- `sqrt_cross_fiber_eq_routed_prime_filter` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:16`
- `sqrt_rejected_quotient_not_prime` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:32`
- `sqrt_quotient_routed_rejected_partition` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:44`
- `sqrt_composite_fiber_corrected_partition` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:57`
- `sqrt_routed_quotient_sum_eq_rough_incidence` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:77`
- `sqrt_quotient_conservation` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:98`
- `sqrt_routed_composite_sum` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:109`
- `sqrt_cross_add_composite_eq_total` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:126`
- `sqrt_composite_sum_corrected` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:133`
- `sqrt_cross_eq_total_sub_routing` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:144`
- `sqrt_cross_bound_of_composite_lower` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:154`
- `sqrt_cross_bound_of_rejected_lower` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:162`
- `sqrt_rejected_card_lower_of_small_primes` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:172`
- `sqrt_cross_le_total` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:184`
- `sqrt_cross_card_le_capacity_sub_routing` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:191`
- `prime_squareCell_of_quotient_routing_budget` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:201`
- `sqrt_quotient_sum_split_owner_range` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:212`
- `primeAnchor_quotient_range_eq_floor` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:221`
- `sqrt_cross_fiber_card_le_odd_span` — `DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean:227`

## DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient

- `paritySafeCanonicalSupportPrime` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:35`
- `paritySafeCanonicalSupportPrime_mem_activeSupport` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:41`
- `paritySafeCanonicalSupportPrime_packet` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:50`
- `paritySafeSupportExcess_seat_eq_quotientCoSupport_card` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:75`
- `paritySafeSupportExcess_eq_covered_quotientCoSupport_sum` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:98`
- `paritySafeCanonicalQuotientCoSupportIncidences` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:122`
- `paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:131`
- `paritySafeCanonicalQuotientCoSupportIncidence_packet` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:209`
- `paritySafeDirectionDepth_false_beam_five_two` — `DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean:260`

## DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit

- `squareAnchorWheelProjection` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:32`
- `squareShellWheelProjection` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:36`
- `squareShellWheelProjection_eq_anchor_add` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:40`
- `squareAnchorWheelProjection_succ` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:50`
- `squareAnchorWheelProjection_add_mul_period` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:61`
- `squareShellWheelProjection_add_mul_period` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:85`
- `reservedByPrimeBasis_projection_iff` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:112`
- `not_reservedByPrimeBasis_projection_iff` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:132`
- `not_reserved_iff_projection_wheelSurvivor` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:140`
- `squareShell_not_reserved_iff_projection_survivor` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:171`
- `primeBasisWheelProjection_insert_fresh_then_old` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:186`
- `squareShellWheelProjection_insert_fresh_projects_old` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:204`
- `squareAnchorWheelProjection_two_three_four` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:220`
- `squareShellWheelProjection_two_three_four_one` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:226`
- `squareShellWheelProjection_two_three_five_four_one` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean:232`

## DkMath.NumberTheory.PrimorialUniverse.WheelProjection

- `primeBasisWheelProjection` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:32`
- `primeBasisWheelProjection_lift` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:36`
- `enlargedWheelSurvivor_projects_to_oldSurvivor` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:47`
- `oldWheelSurvivor_has_enlargedLift` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:66`
- `primeBasisWheelProjectionFiber` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:91`
- `primeBasisWheelProjectionFiber_eq_liftImage` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:97`
- `card_primeBasisWheelProjectionFiber` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:139`
- `primeBasisWheelProjection_reflect_insert_fresh` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:162`
- `primeBasisWheelProjectionFiber_two_three_five_one` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:210`
- `primeBasisWheelProjectionFiber_two_three_five_five` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:240`
- `card_primeBasisWheelProjectionFiber_two_three_five` — `DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean:270`

## DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape

- `IsFinitePrimeBasis` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:35`
- `finitePrimeBasisProduct` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:39`
- `ReservedByPrimeBasis` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:43`
- `finitePrimeBasisEscapePoint` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:47`
- `PrimeSupportContainedIn` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:51`
- `reservedByPrimeBasis_iff` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:54`
- `finitePrimeBasisProduct_ne_zero` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:58`
- `mem_dvd_finitePrimeBasisProduct` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:67`
- `member_not_dvd_finitePrimeBasisEscapePoint` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:76`
- `finitePrimeBasisEscapePoint_not_reserved` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:88`
- `one_lt_finitePrimeBasisEscapePoint` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:96`
- `exists_new_prime_divisor_of_finitePrimeBasis` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:112`
- `finitePrimeBasis_not_globally_reserving` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:127`
- `finitePrimeBasis_has_prime_outside` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:135`
- `newPrime_mul_not_primeSupportContainedIn` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:150`
- `finitePrimeBasisEscapePoint_not_primeSupportContainedIn` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:158`
- `finitePrimeBasisProduct_two_three` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:168`
- `finitePrimeBasisEscapePoint_two_three` — `DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean:172`

## DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization

- `IsCommonMultipleOfPrimeBasis` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:35`
- `finitePrimeBasisProduct_isCommonMultiple` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:38`
- `finitePrimeBasisProduct_dvd_of_commonMultiple` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:48`
- `finitePrimeBasisProduct_dvd_iff_commonMultiple` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:78`
- `reservedByPrimeBasis_add_mul_period_iff` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:90`
- `not_reserved_add_mul_period_iff` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:112`
- `finitePrimeBasisProduct_two_three_five` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:121`
- `finitePrimeBasisProduct_two_three_five_seven` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:125`
- `reservedByPrimeBasis_two_three_five_period_regression` — `DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean:129`

## DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber

- `squareAnchorPhaseFiber` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:34`
- `mem_squareAnchorPhaseFiber` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:40`
- `prime_not_dvd_coprime_anchor` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:48`
- `prime_anchor_cast_ne_zero` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:61`
- `primeSign_plus_ne_minus_of_coprime_anchor` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:72`
- `squareAnchorMinusPrimeSet` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:100`
- `mem_squareAnchorMinusPrimeSet` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:106`
- `modEq_finitePrimeBasisProduct_of_forall_modEq` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:113`
- `squareAnchorPhaseFiber_eq_of_minusPrimeSet_eq` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:149`
- `exists_phaseFiber_anchor_with_minusPrimeSet` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:224`
- `squareAnchorPhaseFiber_card_of_coprime_anchor` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:262`
- `squareAnchorPhaseFiber_two_three_five_regression` — `DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean:327`

## DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge

- `finitePrimeBasis_subset_primeScalesUpTo_product` — `DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean:63`
- `prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody` — `DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean:83`

## DkMath.NumberTheory.Primitive.PrimeWorldResidues

- `primeWorldResidues` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:33`
- `mem_primeWorldResidues` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:38`
- `mem_primeWorldResidues_iff_supportDisjointFrom` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:46`
- `lt_primeWorldModulus_of_mem_primeWorldResidues` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:54`
- `supportDisjointFrom_of_mem_primeWorldResidues` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:60`
- `exists_primeWorldChild_coordinates_of_lt_mul_modulus` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:80`
- `lt_insert_modulus_of_mem_refinedSurvivingSeats` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:103`
- `mem_refined_primeWorldResidues_iff` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:142`
- `refinedSurvivingSeats_primeWorldResidues_eq` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:178`
- `card_primeWorldResidues_insert` — `DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean:191`

Mathlib: `Nat.minFac_le_of_dvd`, `Nat.minFac_prime`, `Nat.ModEq.add_left_cancel`, `Nat.modEq_iff_dvd'`, `Finset.card_eq_sum_card_fiberwise`, `Finset.mul_prod_erase`, `Nat.coprime_prod_right_iff`, and the existing finite-prime divisibility product APIs. No new CRT implementation is needed.

## Reuse decisions

- Basic/Wave: preserve the 2n open-shell offsets and both covered/escaping finite carriers.
- Frontier/PrimorialWheelBridge: point primality iff not covered; the reservation dictionary is valid with an empty basis, whereas survivor equivalence uses n≥2.
- GnomonSuccessor/SupportTurnover: reuse lower odd-gnomon and upper 2(n+1) displacements and exact prime-threshold support intersections.
- ParitySafeFullCoverCapacityFrontier: reuse `paritySafeUncoveredCandidates_eq_empty_of_fullyCovered`; add no new capacity estimate.
- SqrtRoughCensus/QuotientConservation: reuse complete classification and the Rejected correction without enlarging the reduced quotient carrier.
- SupportExcessQuotient: existing `paritySafeCanonicalSupportPrime` is min' on the restricted support; prove agreement with the whole-point minFac owner.
- PrimorialUniverse: product synchronization and projection already encode the CRT state. No duplicate CRT or primorial carrier.
- Primitive.PrimeWorldResidues: its product-period framework already exists; no replacement primitive primorial is needed.
- Additional transition dependency: `DkMath.NumberTheory.Legendre.CyclotomicPersistence.not_dvd_oddGnomon_succ` is reused for the three-lower support exclusion.
- Existing regressions: `primorialWheelBridge_four_one`, `rejected_eleven_packet`, `rejected_eleven`, `repeated_eight_key`, `repeated_lower_key`, `repeated_upper_key`, `triple_key_nineteen`, `quotient1031_uncovered_lower`, and `quotient1031_structural_endpoint` are linked by new kernel theorems.

## New declaration coverage

The generated manifest [declaration coverage](logs/declaration-coverage-016.json) is authoritative for all 61 production and 26 regression/calibration declarations. Exact names and source locations:

- `DkMath.NumberTheory.Legendre.open_shell_card_add_one_eq_oddGnomon` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:18`
- `DkMath.NumberTheory.Legendre.three_consecutive_odd_gnomons` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:22`
- `DkMath.NumberTheory.Legendre.squareResidueCoverFiber` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:30`
- `DkMath.NumberTheory.Legendre.mem_squareResidueCoverFiber` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:33`
- `DkMath.NumberTheory.Legendre.coveredSquareOffsets_eq_residue_union` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:39`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_residue_union` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:51`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_pointwise_forbidden_residue` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:64`
- `DkMath.NumberTheory.Legendre.squareShellWheelImage` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:77`
- `DkMath.NumberTheory.Legendre.mem_squareShellWheelImage` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:80`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_wheel_image_reserved` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:84`
- `DkMath.NumberTheory.Legendre.not_fullyCovered_iff_wheel_image_survivor` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:96`
- `DkMath.NumberTheory.Legendre.SquareAnchorWheelFullyReserved` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:113`
- `DkMath.NumberTheory.Legendre.squareAnchorWheelFullyReserved_iff_full` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:118`
- `DkMath.NumberTheory.Legendre.squareResidueCoverOwner` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:131`
- `DkMath.NumberTheory.Legendre.squareResidueCoverOwner_eq_two_iff` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:134`
- `DkMath.NumberTheory.Legendre.squareResidueCoverOwner_packet` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:152`
- `DkMath.NumberTheory.Legendre.squareResidueOwnerFiber` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:171`
- `DkMath.NumberTheory.Legendre.residue_owner_fibers_disjoint` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:174`
- `DkMath.NumberTheory.Legendre.coveredSquareOffsets_eq_owner_union` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:180`
- `DkMath.NumberTheory.Legendre.residue_owner_fiber_sum` — `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:194`
- `DkMath.NumberTheory.Legendre.squareShellWheelProjection_eq_iff_modEq` — `DkMath/NumberTheory/Legendre/SquareShellWheelPeriod.lean:17`
- `DkMath.NumberTheory.Legendre.squareShellWheelProjection_injOn_iff` — `DkMath/NumberTheory/Legendre/SquareShellWheelPeriod.lean:25`
- `DkMath.NumberTheory.Legendre.squareShell_period_exceeds_width` — `DkMath/NumberTheory/Legendre/SquareShellWheelPeriod.lean:60`
- `DkMath.NumberTheory.Legendre.squareShellWheelProjection_injOn_classification` — `DkMath/NumberTheory/Legendre/SquareShellWheelPeriod.lean:118`
- `DkMath.NumberTheory.Legendre.squareShellWheelImage_card_of_injective` — `DkMath/NumberTheory/Legendre/SquareShellWheelPeriod.lean:126`
- `DkMath.NumberTheory.Legendre.squareOffsetPrimeSupport_eq_activeSupport` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:19`
- `DkMath.NumberTheory.Legendre.escapingSquareOffsets_eq_paritySafeUncovered` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:32`
- `DkMath.NumberTheory.Legendre.squareShellWheelSurvivorImage` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:55`
- `DkMath.NumberTheory.Legendre.squareShell_survivor_filter_eq_image_escaping` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:60`
- `DkMath.NumberTheory.Legendre.squareShell_survivor_card_eq_uncovered` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:77`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_uncovered_empty` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:89`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_rough_zero_card` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:102`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_no_wheel_image_survivor` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:106`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_all_support_nonempty` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:111`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_collapsed_census` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:115`
- `DkMath.NumberTheory.Legendre.sqrt_counterexample_balance_with_uncovered` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:125`
- `DkMath.NumberTheory.Legendre.fullyCovered_iff_corrected_balance` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:136`
- `DkMath.NumberTheory.Legendre.prime_squareCell_of_corrected_counterexample_gap` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:147`
- `DkMath.NumberTheory.Legendre.squareAnchor_counterexample_packet` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:159`
- `DkMath.NumberTheory.Legendre.squareResidueCoverOwner_eq_paritySafeCanonical` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:187`
- `DkMath.NumberTheory.Legendre.squareResidueCoverOwner_eq_of_least_active` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:207`
- `DkMath.NumberTheory.Legendre.sqrt_cube_residue_owner` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:218`
- `DkMath.NumberTheory.Legendre.sqrt_cross_residue_owner` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:226`
- `DkMath.NumberTheory.Legendre.sqrt_repeated_residue_owner` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:234`
- `DkMath.NumberTheory.Legendre.sqrt_triple_residue_owner` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:246`
- `DkMath.NumberTheory.Legendre.sqrt_small_prime_dvd_product_iff_quotient` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:260`
- `DkMath.NumberTheory.Legendre.sqrt_small_basis_reservation_product_iff` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:272`
- `DkMath.NumberTheory.Legendre.sqrt_rejected_iff_quotient_wheel_reserved` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:283`
- `DkMath.NumberTheory.Legendre.sqrt_two_level_reservation_packet` — `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:295`
- `DkMath.NumberTheory.Legendre.squareAnchor_old_basis_succ` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:18`
- `DkMath.NumberTheory.Legendre.squareAnchor_prime_threshold_projects_old` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:25`
- `DkMath.NumberTheory.Legendre.successorThresholdInsert_squareOffset` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:35`
- `DkMath.NumberTheory.Legendre.residue_owner_persistence_mem_inter` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:40`
- `DkMath.NumberTheory.Legendre.residue_owner_persistence_lower` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:53`
- `DkMath.NumberTheory.Legendre.residue_owner_changes_lower` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:64`
- `DkMath.NumberTheory.Legendre.residue_owner_persistence_upper` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:87`
- `DkMath.NumberTheory.Legendre.residue_owner_persistence_prime_upper` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:96`
- `DkMath.NumberTheory.Legendre.residue_owner_changes_prime_upper_odd` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:106`
- `DkMath.NumberTheory.Legendre.residue_owner_no_three_lower` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:121`
- `DkMath.NumberTheory.Legendre.fullyCovered_three_lower_owner_change` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:147`
- `DkMath.NumberTheory.Legendre.primorial_sqrt_address` — `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:157`
- `DkMathTest.LegendreResidueCoverRegression.small_periods` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:21`
- `DkMathTest.LegendreResidueCoverRegression.small_collisions` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:31`
- `DkMathTest.LegendreResidueCoverRegression.three_width_equal_period_injective` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:40`
- `DkMathTest.LegendreResidueCoverRegression.four_basis_and_image` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:44`
- `DkMathTest.LegendreResidueCoverRegression.four_survivor_filter` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:55`
- `DkMathTest.LegendreResidueCoverRegression.four_multiplicity` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:61`
- `DkMathTest.LegendreResidueCoverRegression.four_one_residue_and_survivor` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:68`
- `DkMathTest.LegendreResidueCoverRegression.one_carrier_boundary` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:76`
- `DkMathTest.LegendreResidueCoverRegression.repeated_eight_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:98`
- `DkMathTest.LegendreResidueCoverRegression.repeated_prime_twentyNine_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:105`
- `DkMathTest.LegendreResidueCoverRegression.repeated_thirteen_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:111`
- `DkMathTest.LegendreResidueCoverRegression.triple_nineteen_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:115`
- `DkMathTest.LegendreResidueCoverRegression.cube_cross_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:120`
- `DkMathTest.LegendreResidueCoverRegression.rejected_eleven_two_levels` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:124`
- `DkMathTest.LegendreResidueCoverRegression.three_lower_owners` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:134`
- `DkMathTest.LegendreResidueCoverRegression.lower_support_persists_without_owner` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:145`
- `DkMathTest.LegendreResidueCoverRegression.sqrt_primorial_address_not_above_anchor` — `DkMathTest/NumberTheory/LegendreResidueCoverRegression.lean:153`
- `DkMathTest.LegendreResidueCoverCalibration.near_miss_five_escape` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:19`
- `DkMathTest.LegendreResidueCoverCalibration.near_miss_five_survivors` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:29`
- `DkMathTest.LegendreResidueCoverCalibration.near_miss_five_uncovered` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:33`
- `DkMathTest.LegendreResidueCoverCalibration.near_miss_five_anchor_image` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:37`
- `DkMathTest.LegendreResidueCoverCalibration.residue1031_not_full` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:46`
- `DkMathTest.LegendreResidueCoverCalibration.residue1031_wheel_survivor` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:53`
- `DkMathTest.LegendreResidueCoverCalibration.residue1031_projected_survivor_lower` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:57`
- `DkMathTest.LegendreResidueCoverCalibration.residue1031_corrected_balance_fails` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:61`
- `DkMathTest.LegendreResidueCoverCalibration.residue1031_preserved_endpoint` — `DkMathTest/NumberTheory/LegendreResidueCoverCalibration.lean:68`
