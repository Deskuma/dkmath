# Source inventory 017

The previous finite-difference audit was read in full:
`docs/dev/NumberTheory-PrimitiveStructure-260822-v0/primitive-finite-difference-invariant-audit-260825.md`.
It closes the duplicate delta/derivative route: no prime-wave or coverage provider follows from these identities alone.

The live checkout was clean at the start of this checkpoint. Existing reflection search found no equivalent shell fold definition. CenteredPair already supplies its coordinates, gap and common-divisor dictionary. SquareGnomon additionally already supplies the generic degree-two kernel, area, scale and second-step identities; reuse them.

## DkMath.CosmicFormula.CosmicDifferenceKernel

- `delta` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:21`
- `cosmicKernel` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:30`
- `delta_zero_right` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:34`
- `delta_add` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:39`
- `delta_sub` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:45`
- `delta_smul` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:51`
- `delta_mul` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:62`
- `delta_finset_sum` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:72`
- `cosmicKernel_eq` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:82`
- `cosmicKernel_add` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:87`
- `cosmicKernel_sub` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:93`
- `cosmicKernel_smul` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:99`
- `cosmicKernel_finset_sum` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:107`
- `cosmicKernel_mul` at `DkMath/CosmicFormula/CosmicDifferenceKernel.lean:123`

## DkMath.CosmicFormula.CosmicDerivativePower

- `powerKernel` at `DkMath/CosmicFormula/CosmicDerivativePower.lean:26`
- `powerKernel_eq_GN_swap` at `DkMath/CosmicFormula/CosmicDerivativePower.lean:34`
- `sub_pow_eq_u_mul_powerKernel` at `DkMath/CosmicFormula/CosmicDerivativePower.lean:48`
- `sub_eq_u_mul_powerKernel` at `DkMath/CosmicFormula/CosmicDerivativePower.lean:65`
- `cosmicKernel_pow_eq_powerKernel_of_ne_zero` at `DkMath/CosmicFormula/CosmicDerivativePower.lean:73`

## DkMath.CosmicFormula.CosmicFormulaDerivativeBridge

- `delta_pow_two_eq_u_mul_powerKernel_two` at `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean:16`
- `cosmic_formula_unit_eq_delta_pow_two_sub_two_mul` at `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean:20`
- `cosmic_formula_unit_eq_u_mul_powerKernel_two_sub_two_mul` at `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean:26`
- `cosmic_formula_unit_eq_u_mul_powerKernel_two_gap` at `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean:31`
- `cosmic_formula_unit_eq_u_sq_from_derivative_bridge` at `DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean:37`

## DkMath.CosmicFormula.CosmicFormulaBasic

- `cosmic_formula_one` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:15`
- `cosmic_formula_one_alt` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:20`
- `cosmic_formula_unit` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:25`
- `cosmic_formula_unit_alt` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:30`
- `cosmic_formula_unit_one` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:35`
- `cosmic_formula` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:40`
- `cosmic_formula_one_eq_unit_one` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:45`
- `cosmic_formula_one_eq_alt` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:51`
- `cosmic_formula_unit_eq_alt` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:57`
- `cosmic_formula_one_theorem` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:65`
- `cosmic_formula_unit_theorem` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:73`
- `cosmic_formula_one_func` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:82`
- `cosmic_formula_unit_func` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:88`
- `cosmic_formula_one_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:95`
- `cosmic_formula_unit_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:102`
- `cosmic_formula_one_func_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:109`
- `cosmic_formula_unit_func_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:118`
- `cosmic_formula_unit_sub` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:127`
- `cosmic_formula_unit_sub_eq` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:130`
- `cosmic_formula_one_sub_eq` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:135`
- `N` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:140`
- `P` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:141`
- `cosmic_formula_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:143`
- `cosmic_formula_sub_from_add` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:150`
- `cosmic_formula_unit_eq_sub` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:167`
- `cosmic_formula_one_eq_sub` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:176`
- `cosmic_formula_unit_sub_u0` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:195`
- `cosmic_formula_unit_sub_x0` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:205`
- `N_x0` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:213`
- `P_x0` at `DkMath/CosmicFormula/CosmicFormulaBasic.lean:218`

## DkMath.CosmicFormula.CosmicFormulaBinom

- `G` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:75`
- `Big` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:79`
- `Gap` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:82`
- `Body` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:85`
- `mul_G_eq_GZ` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:94`
- `Body_eq_GZ` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:109`
- `big_is_body_and_gap` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:118`
- `cosmic_id` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:155`
- `cosmic_formula_binom` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:188`
- `cosmic_id` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:194`
- `Z` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:228`
- `Z` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:231`
- `Z_eq_zero` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:235`
- `f` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:247`
- `f_eq_pow_sub` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:256`
- `R` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:270`
- `f_eq_relation` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:279`
- `f_eq_zero_iff` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:294`
- `dim_G_iff` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:299`
- `GN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:323`
- `GN_eq_sum` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:332`
- `GN_eq_G` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:337`
- `G_eq_GN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:342`
- `BigN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:348`
- `GapN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:351`
- `BodyN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:354`
- `cosmic_id_csr` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:358`
- `cosmic_id_csr` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:374`
- `add_pow_gap_factor` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:383`
- `bigN_ne_xpow_add_gapN_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:393`
- `xpow_add_gapN_lt_bigN_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:405`
- `xpow_lt_bodyN_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:417`
- `bodyN_pos_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:430`
- `GN_ne_zero_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:441`
- `one_le_GN_nat_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:455`
- `body_not_perfect_pow_of_squarefree_GN` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:497`
- `add_pow_tail_u2_d3` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:546`
- `add_pow_tail_u2_d3_nat_dvd` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:554`
- `two_gap_xy_factor_d3` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:576`
- `two_gap_xy_factor_d3_nat_dvd` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:584`
- `two_gap_xy_factor` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:606`
- `two_gap_xy_factor_nat_dvd` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:661`
- `two_gap_xy_factor_of_two_le` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:683`
- `add_pow_ne_sum_pows_nat_of_two_le_binom` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:701`
- `add_pow_gt_sum_pows_nat_of_two_le_binom` at `DkMath/CosmicFormula/CosmicFormulaBinom.lean:709`

## DkMath.CosmicFormula.SquareGnomon

- `squareGnomonKernel` at `DkMath/CosmicFormula/SquareGnomon.lean:76`
- `squareGnomon` at `DkMath/CosmicFormula/SquareGnomon.lean:80`
- `squareGnomonKernel_eq_GTail` at `DkMath/CosmicFormula/SquareGnomon.lean:84`
- `squareGnomonKernel_eq_two_mul_add` at `DkMath/CosmicFormula/SquareGnomon.lean:89`
- `squareGnomon_eq_mul_two_mul_add` at `DkMath/CosmicFormula/SquareGnomon.lean:96`
- `core_add_squareGnomon_eq_next_square` at `DkMath/CosmicFormula/SquareGnomon.lean:101`
- `bodyN_two_add_squareGnomon` at `DkMath/CosmicFormula/SquareGnomon.lean:110`
- `bigN_two_step_fixedGap` at `DkMath/CosmicFormula/SquareGnomon.lean:120`
- `squareGnomonKernel_step` at `DkMath/CosmicFormula/SquareGnomon.lean:130`
- `squareGnomon_step` at `DkMath/CosmicFormula/SquareGnomon.lean:137`
- `squareGnomon_scale` at `DkMath/CosmicFormula/SquareGnomon.lean:144`

## DkMath.NumberTheory.Legendre.Basic

- `SquareCell` at `DkMath/NumberTheory/Legendre/Basic.lean:32`
- `SquareOffset` at `DkMath/NumberTheory/Legendre/Basic.lean:36`
- `SquareOffsetForbiddenBy` at `DkMath/NumberTheory/Legendre/Basic.lean:40`
- `SquareOffsetCovered` at `DkMath/NumberTheory/Legendre/Basic.lean:44`
- `squareOffsetCovered_iff_exists_prime_dvd` at `DkMath/NumberTheory/Legendre/Basic.lean:48`
- `supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` at `DkMath/NumberTheory/Legendre/Basic.lean:60`
- `squareAnchorForbiddenResidue` at `DkMath/NumberTheory/Legendre/Basic.lean:75`
- `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue` at `DkMath/NumberTheory/Legendre/Basic.lean:79`
- `squareOffsetPrimeSupport` at `DkMath/NumberTheory/Legendre/Basic.lean:114`
- `mem_squareOffsetPrimeSupport` at `DkMath/NumberTheory/Legendre/Basic.lean:119`
- `squareOffsetCovered_iff_primeSupport_nonempty` at `DkMath/NumberTheory/Legendre/Basic.lean:128`
- `squareOffsetCovered_iff_primeSupport_card_pos` at `DkMath/NumberTheory/Legendre/Basic.lean:141`
- `squareOffsetForbiddenBy_pair_iff_product_dvd` at `DkMath/NumberTheory/Legendre/Basic.lean:147`
- `squareOffsetForbiddenBy_pair_iff_product_phase` at `DkMath/NumberTheory/Legendre/Basic.lean:159`
- `SquareOffsetOverlap` at `DkMath/NumberTheory/Legendre/Basic.lean:182`
- `squareOffsetOverlap_iff_exists_distinct_support` at `DkMath/NumberTheory/Legendre/Basic.lean:186`
- `squareCell_iff_exists_squareOffset` at `DkMath/NumberTheory/Legendre/Basic.lean:215`
- `LegendreConjecture` at `DkMath/NumberTheory/Legendre/Basic.lean:238`
- `SquareAnchoredSupportEscape` at `DkMath/NumberTheory/Legendre/Basic.lean:245`
- `squareOffsets` at `DkMath/NumberTheory/Legendre/Basic.lean:251`
- `mem_squareOffsets` at `DkMath/NumberTheory/Legendre/Basic.lean:255`
- `card_squareOffsets` at `DkMath/NumberTheory/Legendre/Basic.lean:261`

## DkMath.NumberTheory.Legendre.CenteredPair

- `centeredLeftOffset` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:27`
- `centeredRightOffset` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:30`
- `squareOffset_centeredLeftOffset` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:35`
- `squareOffset_centeredRightOffset` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:42`
- `centeredPoint_difference` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:51`
- `centeredCommonDivisor_iff` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:61`
- `mem_common_squareOffsetPrimeSupport_iff` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:79`
- `disjoint_squareOffsetPrimeSupport_centeredPair` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:100`
- `exists_distinct_centeredPair_primeSupport_of_fullyCovered` at `DkMath/NumberTheory/Legendre/CenteredPair.lean:119`

## DkMath.NumberTheory.Legendre.OldSupportGcd

- `gcd_squarePoints_dvd_orderedOffsetGap` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:34`
- `disjoint_squareOffsetPrimeSupport_iff_gcd_supportDisjointFrom` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:54`
- `disjoint_squareOffsetPrimeSupport_iff_gcd_coprime_primeWorldModulus` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:83`
- `gcd_squarePoints_lt_twice_anchor` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:96`
- `disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:112`
- `prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:186`
- `oldSupportCapacity_strictness_gcd_three_one_six` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:200`
- `PairwiseGcdFreshSeparatedSquareSeatFamily` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:211`
- `pairwiseGcdFreshSeparatedSquareSeatFamily_iff_oldSupportDisjoint` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:220`
- `exists_prime_squareCell_of_pairwiseGcdFreshSeparatedSquareSeatFamily_card_excess` at `DkMath/NumberTheory/Legendre/OldSupportGcd.lean:252`

## DkMath.NumberTheory.Legendre.GnomonSuccessor

- `card_squareOffsets_succ_add_two` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:31`
- `oddGnomon_succ_add_two` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:37`
- `successorThresholdOffsets` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:45`
- `successorThresholdOffsets_subset_squareOffsets_succ` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:49`
- `card_successorThresholdOffsets` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:63`
- `mem_successorThresholdOffsets_iff_threshold_dvd` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:69`
- `card_squareOffsets_succ_sdiff_threshold` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:77`
- `successorThresholdInsert` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:89`
- `successorThresholdInsert_mem_sdiff` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:93`
- `dvd_oddGnomon_of_dvd_adjacent_square_points` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:125`
- `oldPrime_not_common_sameOffset` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:138`
- `successorThresholdInsert_lower_additive_displacement` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:149`
- `successorThresholdInsert_upper_additive_displacement` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:161`
- `dvd_oddGnomon_of_dvd_reindexed_lower_common` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:169`
- `dvd_two_mul_succ_of_dvd_reindexed_upper_common` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:178`
- `primeScalesUpTo_31_eq_insert` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:190`
- `successorThresholdOffsets_30_eq` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:195`
- `card_squareOffsets_31_sdiff_threshold_30` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:199`
- `successor_reindex_30_6_mismatch` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:205`
- `successor_reindex_30_7_mismatch` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:220`
- `oldPrime_30_not_common_lower_reindex` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:235`
- `oldPrime_30_common_upper_reindex_dvd_62` at `DkMath/NumberTheory/Legendre/GnomonSuccessor.lean:251`

## DkMath.NumberTheory.Legendre.GnomonSupportTurnover

- `mem_reindexed_primeSupport_inter_lower_iff` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:27`
- `reindexed_primeSupport_inter_lower_eq_filter` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:57`
- `mem_reindexed_primeSupport_inter_upper_iff` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:70`
- `reindexed_primeSupport_inter_upper_eq_filter` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:100`
- `oldPrime_dvd_two_mul_succ_imp_eq_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:115`
- `oldPrime_dvd_two_mul_succ_iff_eq_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:131`
- `mem_reindexed_primeSupport_inter_upper_imp_eq_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:143`
- `reindexed_primeSupport_inter_upper_eq_filter_eq_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:157`
- `disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:180`
- `disjoint_reindexed_primeSupport_upper_of_prime_succ_of_not_dvd_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:200`
- `disjoint_reindexed_primeSupport_lower_30` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:219`
- `mem_reindexed_primeSupport_inter_upper_30_imp_eq_two` at `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean:226`

## DkMath.NumberTheory.Legendre.GnomonResidueCover

- `open_shell_card_add_one_eq_oddGnomon` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:18`
- `three_consecutive_odd_gnomons` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:22`
- `squareResidueCoverFiber` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:30`
- `mem_squareResidueCoverFiber` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:33`
- `coveredSquareOffsets_eq_residue_union` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:39`
- `fullyCovered_iff_residue_union` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:51`
- `fullyCovered_iff_pointwise_forbidden_residue` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:64`
- `squareShellWheelImage` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:77`
- `mem_squareShellWheelImage` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:80`
- `fullyCovered_iff_wheel_image_reserved` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:84`
- `not_fullyCovered_iff_wheel_image_survivor` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:96`
- `SquareAnchorWheelFullyReserved` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:113`
- `squareAnchorWheelFullyReserved_iff_full` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:118`
- `squareResidueCoverOwner` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:131`
- `squareResidueCoverOwner_eq_two_iff` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:134`
- `squareResidueCoverOwner_packet` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:152`
- `squareResidueOwnerFiber` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:171`
- `residue_owner_fibers_disjoint` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:174`
- `coveredSquareOffsets_eq_owner_union` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:180`
- `residue_owner_fiber_sum` at `DkMath/NumberTheory/Legendre/GnomonResidueCover.lean:194`

## DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket

- `squareOffsetPrimeSupport_eq_activeSupport` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:19`
- `escapingSquareOffsets_eq_paritySafeUncovered` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:32`
- `squareShellWheelSurvivorImage` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:55`
- `squareShell_survivor_filter_eq_image_escaping` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:60`
- `squareShell_survivor_card_eq_uncovered` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:77`
- `fullyCovered_iff_uncovered_empty` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:89`
- `fullyCovered_iff_rough_zero_card` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:102`
- `fullyCovered_iff_no_wheel_image_survivor` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:106`
- `fullyCovered_iff_all_support_nonempty` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:111`
- `fullyCovered_iff_collapsed_census` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:115`
- `sqrt_counterexample_balance_with_uncovered` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:125`
- `fullyCovered_iff_corrected_balance` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:136`
- `prime_squareCell_of_corrected_counterexample_gap` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:147`
- `squareAnchor_counterexample_packet` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:159`
- `squareResidueCoverOwner_eq_paritySafeCanonical` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:187`
- `squareResidueCoverOwner_eq_of_least_active` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:207`
- `sqrt_cube_residue_owner` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:218`
- `sqrt_cross_residue_owner` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:226`
- `sqrt_repeated_residue_owner` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:234`
- `sqrt_triple_residue_owner` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:246`
- `sqrt_small_prime_dvd_product_iff_quotient` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:260`
- `sqrt_small_basis_reservation_product_iff` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:272`
- `sqrt_rejected_iff_quotient_wheel_reserved` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:283`
- `sqrt_two_level_reservation_packet` at `DkMath/NumberTheory/Legendre/SquareAnchorCounterexamplePacket.lean:295`

## DkMath.NumberTheory.Legendre.GnomonPrimorialTransition

- `squareAnchor_old_basis_succ` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:18`
- `squareAnchor_prime_threshold_projects_old` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:25`
- `successorThresholdInsert_squareOffset` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:35`
- `residue_owner_persistence_mem_inter` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:40`
- `residue_owner_persistence_lower` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:53`
- `residue_owner_changes_lower` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:64`
- `residue_owner_persistence_upper` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:87`
- `residue_owner_persistence_prime_upper` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:96`
- `residue_owner_changes_prime_upper_odd` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:106`
- `residue_owner_no_three_lower` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:121`
- `fullyCovered_three_lower_owner_change` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:147`
- `primorial_sqrt_address` at `DkMath/NumberTheory/Legendre/GnomonPrimorialTransition.lean:157`

## DkMath.NumberTheory.Legendre.CyclotomicPersistence

- `cyclotomicShiftedEval_two_eq_oddGnomon` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:24`
- `mem_lower_commonSupport_iff_cyclotomic` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:31`
- `not_dvd_coordinates_of_dvd_oddGnomon` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:41`
- `dvd_oddGnomon_iff_primeOrder_eq_two` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:55`
- `dvd_cyclotomic_lower_iff_primeOrder_eq_two` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:79`
- `mem_lower_commonSupport_iff_primeOrder_eq_two` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:87`
- `dvd_oddGnomon_iff_modEq_half` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:97`
- `dvd_oddGnomon_iff_eq_half_add_mul` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:126`
- `modEq_of_dvd_oddGnomon` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:142`
- `dvd_oddGnomon_iff_modEq_of_dvd` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:149`
- `dvd_four_mul_offset_add_one_of_lower_persistence` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:158`
- `not_dvd_oddGnomon_succ` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:171`
- `lowerPrimeAddressOffsets` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:180`
- `shellFrequencyCap` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:185`
- `lowerPrimeAddressOffsets_card_le` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:190`
- `lowerPrimeAddressOffsets_period_card_le_one` at `DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean:217`

## DkMath.Gnomon.Algebra

- `oddGnomon` at `DkMath/Gnomon/Algebra.lean:31`
- `squareGnomonBand` at `DkMath/Gnomon/Algebra.lean:35`
- `petalMul` at `DkMath/Gnomon/Algebra.lean:39`
- `oddGnomon_zero` at `DkMath/Gnomon/Algebra.lean:42`
- `oddGnomon_succ` at `DkMath/Gnomon/Algebra.lean:45`
- `oddGnomon_pos` at `DkMath/Gnomon/Algebra.lean:50`
- `oddGnomon_odd` at `DkMath/Gnomon/Algebra.lean:54`
- `oddGnomon_injective` at `DkMath/Gnomon/Algebra.lean:58`
- `oddGnomon_eq_one_iff` at `DkMath/Gnomon/Algebra.lean:64`
- `petalMul_zero_left` at `DkMath/Gnomon/Algebra.lean:74`
- `petalMul_zero_right` at `DkMath/Gnomon/Algebra.lean:78`
- `petalMul_comm` at `DkMath/Gnomon/Algebra.lean:82`
- `petalMul_assoc` at `DkMath/Gnomon/Algebra.lean:87`
- `oddGnomon_petalMul` at `DkMath/Gnomon/Algebra.lean:92`
- `square_add_oddGnomon` at `DkMath/Gnomon/Algebra.lean:97`
- `square_add_squareGnomonBand` at `DkMath/Gnomon/Algebra.lean:102`
- `squareGnomonBand_zero` at `DkMath/Gnomon/Algebra.lean:107`
- `squareGnomonBand_unit` at `DkMath/Gnomon/Algebra.lean:111`
- `squareGnomonBand_zero_anchor` at `DkMath/Gnomon/Algebra.lean:115`
- `squareGnomonBand_add` at `DkMath/Gnomon/Algebra.lean:119`
- `squareGnomonBand_eq_sum_shifted_oddGnomon` at `DkMath/Gnomon/Algebra.lean:125`
- `sum_oddGnomon_eq_square` at `DkMath/Gnomon/Algebra.lean:143`
- `sum_odd_eq_square` at `DkMath/Gnomon/Algebra.lean:152`

## DkMath.Gnomon.CosmicBridge

- `GTail_two_one_eq_square_shell` at `DkMath/Gnomon/CosmicBridge.lean:30`
- `oddGnomon_eq_GTail_two_one_unit` at `DkMath/Gnomon/CosmicBridge.lean:36`
- `squareGnomonBand_eq_mul_GTail_two_one` at `DkMath/Gnomon/CosmicBridge.lean:43`
- `square_add_mul_GTail_two_one` at `DkMath/Gnomon/CosmicBridge.lean:51`
- `square_add_squareGnomonBand_eq_mul_GTail_two_one` at `DkMath/Gnomon/CosmicBridge.lean:60`
- `mul_GTail_two_one_add_thickness` at `DkMath/Gnomon/CosmicBridge.lean:67`
- `mul_GTail_two_one_eq_sum_unit_GTail` at `DkMath/Gnomon/CosmicBridge.lean:84`

## Additional exact dependencies

- `Mathlib.NumberTheory.LegendreSymbol.Basic`: `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` and `ZMod.natCast_eq_zero_iff`.
- `Nat.coprime_of_dvd`, `Nat.Prime.dvd_of_dvd_pow`, `Finset.card_bij`, `Nat.le_div_iff_mul_le`.
- Existing `dvd_oddGnomon_iff_modEq_half` and `dvd_oddGnomon_iff_eq_half_add_mul` already provide the odd-prime progression. The exact finite card is a counted specialization, not a new residue framework.
- The generic field adapter is kept outside Legendre; Legendre uses Nat/Int geometry and the existing GTail bridge directly.

## Final duplicate and scope comparison

- Repeated reflection/involution/mirror and literal reflected-offset searches in existing Legendre sources (excluding the three new modules) found no equivalent reflection API. Finset fold-min operations in capacity code are unrelated reductions, not offset involutions.
- Repository-wide searches for the consecutive-square norm, centered norm/gcd interface and the finite-field mod-four lemma found no prior exact centered-fold norm interface. OldSupportGcd supplies gcd/gap divisibility and the 1-or-fresh-prime alternative, but not this exact norm activation or coprime consecutive norms.
- PairOverlap supplies support-pair incidence and overlap corrections; it does not count same least owners on centered fold pairs. The new gap progression aliases lowerPrimeAddressOffsets rather than replacing it.
- Mathlib finite-field step: `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` at `.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/Basic.lean:292`.
- Existing calibration reused: `DkMathTest.LegendreResidueCoverCalibration.near_miss_five_uncovered`, `residue1031_not_full`, `residue1031_projected_survivor_lower` and `residue1031_preserved_endpoint`.
