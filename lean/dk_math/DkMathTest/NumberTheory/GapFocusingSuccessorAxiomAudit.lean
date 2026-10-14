/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing

#print "file: DkMathTest.NumberTheory.GapFocusingSuccessorAxiomAudit"

#print axioms DkMath.NumberTheory.GapFocusing.GN_succ_right
#print axioms DkMath.NumberTheory.GapFocusing.GN_succ_left
#print axioms DkMath.NumberTheory.GapFocusing.GN_succ_unit_anchor
#print axioms DkMath.NumberTheory.GapFocusing.GN_succ_bezout
#print axioms DkMath.NumberTheory.GapFocusing.GN_succ_isCoprime_unit_anchor
#print axioms DkMath.NumberTheory.GapFocusing.dvd_anchor_pow_of_dvd_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.dvd_sum_pow_of_dvd_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.nat_dvd_powers_of_dvd_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.nat_prime_dvd_coordinates_of_dvd_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.nat_one_lt_GN_succ
#print axioms DkMath.NumberTheory.GapFocusing.nat_exists_prime_dvd_GN_succ_not_dvd_GN
#print axioms DkMath.NumberTheory.GapFocusing.dvd_GN_of_dvd_coordinates
#print axioms DkMath.NumberTheory.GapFocusing.nat_prime_dvd_adjacent_GN_iff
#print axioms DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN_iff
#print axioms DkMath.NumberTheory.GapFocusing.isCoprime_adjacent_GN
#print axioms DkMath.NumberTheory.GapFocusing.int_gcd_adjacent_GN_eq_one
#print axioms DkMath.NumberTheory.GapFocusing.GN_polynomial_succ_isCoprime
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_succ_bezout
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_succ_isCoprime
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_successor_interpolation
#print axioms DkMath.NumberTheory.GapFocusing.successor_divisor_layers_disjoint
#print axioms DkMath.NumberTheory.GapFocusing.eq_one_of_adjacent_pow_eq_one
#print axioms DkMath.NumberTheory.GapFocusing.successor_nontrivial_roots_disjoint
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_common_divisor_isUnit
#print axioms DkMath.NumberTheory.GapFocusing.kernelIdeal
#print axioms DkMath.NumberTheory.GapFocusing.kernelIdeal_succ_isCoprime
#print axioms DkMath.NumberTheory.GapFocusing.kernelQuotientSuccessorCRT
#print axioms DkMath.NumberTheory.GapFocusing.kernelQuotientSuccessorCRT_mk
#print axioms DkMath.NumberTheory.GapFocusing.sameUnitPowerClass_iff_mem_powerSubgroup
#print axioms DkMath.NumberTheory.GapFocusing.sameUnitPowerClass_iff_quotient_eq
#print axioms DkMath.NumberTheory.GapFocusing.sameUnitPowerClass_mul_iff_of_coprime
#print axioms DkMath.NumberTheory.GapFocusing.sameUnitPowerClass_successor_iff
#print axioms DkMath.Lib.Algebra.powerSubgroup
#print axioms DkMath.Lib.Algebra.mem_powerSubgroup
#print axioms DkMath.Lib.Algebra.powerSubgroup_zero
#print axioms DkMath.Lib.Algebra.powerSubgroup_one
#print axioms DkMath.Lib.Algebra.coprime_pow_bezout
#print axioms DkMath.Lib.Algebra.exists_mul_pow_of_coprime
#print axioms DkMath.Lib.Algebra.powerSubgroup_sup_eq_top_of_coprime
#print axioms DkMath.Lib.Algebra.powerSubgroup_mul_le_inf
#print axioms DkMath.Lib.Algebra.powerSubgroup_inf_eq_mul_of_coprime
#print axioms DkMath.Lib.Algebra.powerQuotientPair
#print axioms DkMath.Lib.Algebra.powerQuotientPair_apply
#print axioms DkMath.Lib.Algebra.powerQuotientPair_ker
#print axioms DkMath.Lib.Algebra.powerQuotientPair_surjective
#print axioms DkMath.Lib.Algebra.powerQuotientCRT
#print axioms DkMath.Lib.Algebra.powerQuotientCRT_apply_mk
#print axioms DkMath.Lib.Algebra.powerSubgroup_sup_successor
#print axioms DkMath.Lib.Algebra.powerSubgroup_inf_successor
#print axioms DkMath.Lib.Algebra.exists_mul_pow_successor
#print axioms DkMath.Lib.Algebra.powerQuotientSuccessorCRT
#print axioms DkMath.Lib.Algebra.powerQuotientSuccessorCRT_apply_mk
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup_sup_successor
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup_inf_successor
#print axioms DkMath.Lib.Algebra.unitPowerQuotientSuccessorCRT
#print axioms DkMath.Lib.Algebra.unitPowerQuotientSuccessorCRT_apply_mk
