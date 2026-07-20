/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five
import DkMath.FLT.Five.Standalone

#print axioms DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5
#print axioms DkMath.FLT.Five.GN5_one_one_not_fifth_power
#print axioms DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body
#print axioms DkMath.FLT.Five.body5_eq_fifth_power_of_fermat
#print axioms DkMath.FLT.Five.padicValNat_lower_bound_d5
#print axioms DkMath.FLT.Five.padicValNat_clean_body_upper_bound
#print axioms DkMath.FLT.Five.Standalone.add_pow_five_eq_add_mul_GN5

#print axioms DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5
#print axioms DkMath.FLT.Five.not_fifth_power_body_of_clean
#print axioms DkMath.FLT.Five.counterexample_false_of_clean_GN5Channel_by_dvd
#print axioms DkMath.FLT.Five.counterexample_false_of_clean_GN5Channel_by_padicValNat

#print axioms DkMath.FLT.Five.coprime_gap_GN5_of_coprime_of_five_not_dvd
#print axioms DkMath.FLT.Five.branchB_coprime_gap_GN5
#print axioms DkMath.FLT.Five.fifth_power_factor_split
#print axioms DkMath.FLT.Five.branchB_fifth_power_factor_split
#print axioms DkMath.FLT.Five.branchB_false_of_GN5_not_fifth_power

#print axioms DkMath.FLT.Five.coprime_GN5_y_of_coprime
#print axioms DkMath.FLT.Five.exists_branchB_fifthPowerNormalForm
#print axioms DkMath.FLT.Five.branchB_false_of_fifthPowerCore

#print axioms DkMath.FLT.Five.GN5_eq_square_cross_form
#print axioms DkMath.FLT.Five.square_cross_coordinate_change
#print axioms DkMath.FLT.Five.GN5_eq_goldenNorm_squareLink
#print axioms DkMath.FLT.Five.four_mul_goldenNorm_eq_discriminant_five
#print axioms DkMath.FLT.Five.goldenNorm_eq_fifth_power_of_GN5

#print axioms DkMath.FLT.Five.squareGolden_tenth_boundary_base
#print axioms DkMath.FLT.Five.squareGolden_square_discriminant
#print axioms DkMath.FLT.Five.exists_branchB_squareGoldenNormalForm
#print axioms DkMath.FLT.Five.branchB_false_of_squareGoldenCore

#print axioms DkMath.FLT.Five.five_not_dvd_GN5_of_five_not_dvd_gap
#print axioms DkMath.FLT.Five.five_not_dvd_x_of_branchB
#print axioms DkMath.FLT.Five.pow_five_mod_five
#print axioms DkMath.FLT.Five.five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
#print axioms DkMath.FLT.Five.five_dvd_z_sub_x_of_fermat5_of_five_dvd_y
#print axioms DkMath.FLT.Five.five_dvd_x_add_y_of_fermat5_of_five_dvd_z
#print axioms DkMath.FLT.Five.signedBranchA_normalForm_of_branchB
#print axioms DkMath.FLT.Five.branchB_false_of_signedBranchARefuter

#print axioms DkMath.FLT.Five.add_mul_sumGN5_eq_add_pow_five
#print axioms DkMath.FLT.Five.padicValNat_five_eq_one_of_dvd_not_sq
#print axioms DkMath.FLT.Five.padicValNat_carrier_shape_of_mul_eq_fifth
#print axioms DkMath.FLT.Five.signedFiveAdicPacket_of_normalForm
#print axioms DkMath.FLT.Five.signedBranchARefuter_of_fiveAdicCore
#print axioms DkMath.FLT.Five.branchB_false_of_fiveAdicCore

#print axioms DkMath.FLT.Five.signedFiveAdicPacket_gcd_eq_five
#print axioms DkMath.FLT.Five.signedFiveAdicPowerSplit_of_packet
#print axioms DkMath.FLT.Five.signedFiveAdicPowerSplit_of_normalForm
#print axioms DkMath.FLT.Five.signedBranchARefuter_of_powerSplitCore
#print axioms DkMath.FLT.Five.branchB_false_of_powerSplitCore

#print axioms DkMath.FLT.Five.sumGN5_eq_goldenNorm_signed
#print axioms DkMath.FLT.Five.signed_endpoint_square_discriminant
#print axioms DkMath.FLT.Five.signedSquareGoldenExceptionalPacket_of_powerSplit
#print axioms DkMath.FLT.Five.signedSquareGoldenExceptionalPacket_of_normalForm
#print axioms DkMath.FLT.Five.signedBranchARefuter_of_squareGoldenExceptionalCore
#print axioms DkMath.FLT.Five.branchB_false_of_squareGoldenExceptionalCore

#print axioms DkMath.FLT.Five.goldenConj_mul
#print axioms DkMath.FLT.Five.goldenNorm_mul
#print axioms DkMath.FLT.Five.golden_tau_mul_conj
#print axioms DkMath.FLT.Five.exists_goldenTau_factor_of_five_dvd
#print axioms DkMath.FLT.Five.signedGoldenRamifierStrippedPacket_of_exceptional
#print axioms DkMath.FLT.Five.signedGoldenRamifierStrippedPacket_of_powerSplit
#print axioms DkMath.FLT.Five.signedGoldenRamifierStrippedPacket_of_normalForm
#print axioms DkMath.FLT.Five.signedBranchARefuter_of_goldenRamifierStrippedCore
#print axioms DkMath.FLT.Five.branchB_false_of_goldenRamifierStrippedCore

#print axioms DkMath.FLT.Five.goldenUnit_of_norm_eq_one
#print axioms DkMath.FLT.Five.goldenUnit_of_norm_eq_neg_one
#print axioms DkMath.FLT.Five.SignedFiveAdicPowerSplit.coprime_a_b
#print axioms DkMath.FLT.Five.SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
#print axioms DkMath.FLT.Five.goldenNorm_sub_conj
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
#print axioms DkMath.FLT.Five.signedGoldenConjugateCoprimePacket_of_stripped
#print axioms DkMath.FLT.Five.signedGoldenConjugateCoprimePacket_of_normalForm
#print axioms DkMath.FLT.Five.signedBranchARefuter_of_goldenConjugateCoprimeCore
#print axioms DkMath.FLT.Five.branchB_false_of_goldenConjugateCoprimeCore

#print axioms DkMath.FLT.Five.goldenUnit_phi
#print axioms DkMath.FLT.Five.goldenDoubleEmbedding_mul
#print axioms DkMath.FLT.Five.GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
#print axioms DkMath.FLT.Five.goldenUnit_mul
#print axioms DkMath.FLT.Five.goldenUnit_pow
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
#print axioms DkMath.FLT.Five.signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
#print axioms DkMath.FLT.Five.goldenPow_five_fst
#print axioms DkMath.FLT.Five.goldenPow_five_snd
#print axioms DkMath.FLT.Five.golden_unit_four_mul_fifth_snd

#print axioms DkMath.FLT.Five.goldenRat_norm_abs_le_five_sixteen
#print axioms DkMath.FLT.Five.golden_remainder_size_lt
#print axioms DkMath.FLT.Five.exists_golden_quotient_remainder
#print axioms DkMath.FLT.Five.goldenUnit_iff_isUnit
#print axioms DkMath.FLT.Five.goldenCoprimeFactorOfFifthPower
#print axioms DkMath.FLT.Five.signedGoldenFifthPowerUpToUnitCore
#print axioms DkMath.FLT.Five.signedGoldenFiniteUnitSectorCore_of_unitClasses
#print axioms DkMath.FLT.Five.signedGoldenRamifierStrippedCore_of_unitFifthPowerExclusion
#print axioms DkMath.FLT.Five.branchB_false_of_unitFifthPowerExclusion

#print axioms DkMath.FLT.Five.signedGoldenUnitFifthPowerExclusion_iff_strippedCore
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
#print axioms DkMath.FLT.Five.five_dvd_goldenFifthFstPoly_sub_linear
#print axioms DkMath.FLT.Five.five_dvd_goldenNorm_sub_linear_sq
#print axioms DkMath.FLT.Five.signedGolden_nonzero_unitSector_false
#print axioms DkMath.FLT.Five.signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor
#print axioms DkMath.FLT.Five.SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
#print axioms DkMath.FLT.Five.signedGoldenZeroSectorExclusion_of_arithmetic
#print axioms DkMath.FLT.Five.CounterexamplePack.branchB_orientation
#print axioms DkMath.FLT.Five.counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
#print axioms DkMath.FLT.Five.exists_counterexamplePack_of_positive_fermat5
#print axioms DkMath.FLT.Five.positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
#print axioms DkMath.FLT.Five.flt5Target_of_unitClasses_of_zeroArithmetic

#print axioms DkMath.FLT.Five.golden_phi_mul_inv
#print axioms DkMath.FLT.Five.golden_inv_mul_phi
#print axioms DkMath.FLT.Five.goldenUnit_descent
#print axioms DkMath.FLT.Five.goldenUnitFifthClass_mul_phi
#print axioms DkMath.FLT.Five.goldenUnitFifthClass_mul_phiInv
#print axioms DkMath.FLT.Five.goldenUnitFifthClass_of_unit
#print axioms DkMath.FLT.Five.goldenUnitClassesModFifth
#print axioms DkMath.FLT.Five.signedGoldenFiniteUnitSectorCore
#print axioms DkMath.FLT.Five.counterexamplePackRefuter_of_zeroArithmetic
#print axioms DkMath.FLT.Five.positiveFermat5Refuter_of_zeroArithmetic
#print axioms DkMath.FLT.Five.flt5Target_of_zeroArithmetic

-- Certified zero-sector inversion and factorization.
#print axioms DkMath.FLT.Five.goldenZeroSectorCandidate_of_raw
#print axioms DkMath.FLT.Five.goldenZeroSectorInversionPacket
#print axioms DkMath.FLT.Five.GoldenZeroSectorInversionPacket.factor_product
#print axioms DkMath.FLT.Five.GoldenZeroSectorInversionPacket.factor_difference
#print axioms DkMath.FLT.Five.fifth_mod_eleven_cases
#print axioms DkMath.FLT.Five.eleven_dvd_d_of_fifth_add_four_fifth
#print axioms DkMath.FLT.Five.GoldenZeroSectorFactorData.odd_eleven_channel
#print axioms DkMath.FLT.Five.goldenZeroSectorFactorPacket_of_inversion
#print axioms DkMath.FLT.Five.nonempty_goldenZeroSectorFactorPacket
#print axioms DkMath.FLT.Five.goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion

-- Strict golden-lift descent and unconditional closure.
#print axioms DkMath.FLT.Five.goldenZeroSectorLift_norm
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.lift_relPrime_conj
#print axioms DkMath.FLT.Five.five_dvd_norm_of_nonzero_goldenUnitSector
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.fifthRoot_power_split
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.fifthRoot_measure_lt
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.strictDescent
#print axioms DkMath.FLT.Five.goldenZeroSectorDescentPacket_false
#print axioms DkMath.FLT.Five.goldenZeroSectorDescentPacket_of_candidate
#print axioms DkMath.FLT.Five.goldenZeroSectorCandidate_false
#print axioms DkMath.FLT.Five.goldenZeroSectorFactorExclusion
#print axioms DkMath.FLT.Five.goldenZeroSectorArithmeticExclusion_of_factorExclusion
#print axioms DkMath.FLT.Five.goldenZeroSectorArithmeticExclusion
#print axioms DkMath.FLT.Five.flt5Target
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution
