/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing

#print "file: DkMathTest.NumberTheory.GapFocusingAxiomAudit"

#print axioms DkMath.NumberTheory.GapFocusing.focusCoordinates
#print axioms DkMath.NumberTheory.GapFocusing.focused_pow_sub
#print axioms DkMath.NumberTheory.GapFocusing.unfocused_pow_sub
#print axioms DkMath.NumberTheory.GapFocusing.gap_dvd_iff_dvd_defect
#print axioms DkMath.NumberTheory.GapFocusing.focusDefect_cocycle
#print axioms DkMath.NumberTheory.GapFocusing.focusDefect_scale
#print axioms DkMath.NumberTheory.GapFocusing.unfocused_polynomial_remainder
#print axioms DkMath.NumberTheory.GapFocusing.X_dvd_unfocused_iff
#print axioms DkMath.NumberTheory.GapFocusing.focused_quotient_unique
#print axioms DkMath.NumberTheory.GapFocusing.unfocused_constant_unique
#print axioms DkMath.NumberTheory.GapFocusing.focused_quotient_eval_zero
#print axioms DkMath.NumberTheory.GapFocusing.X_sq_dvd_focused_iff
#print axioms DkMath.NumberTheory.GapFocusing.phaseFactor_eq_gap_forall_iff
#print axioms DkMath.NumberTheory.GapFocusing.phaseFactor_polynomial_eq_gap_iff
#print axioms DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod
#print axioms DkMath.NumberTheory.GapFocusing.nthRootsFinset_eq_powers
#print axioms DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod_range
#print axioms DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod_fin
#print axioms DkMath.NumberTheory.GapFocusing.indexed_phase_eq_gap_forall_iff
#print axioms DkMath.NumberTheory.GapFocusing.phaseFactor_eq_gap_iff_of_ne_zero
#print axioms DkMath.NumberTheory.GapFocusing.GN_eq_nontrivial_phase_prod_range
#print axioms DkMath.NumberTheory.GapFocusing.nontrivialRootsFinset_eq_powers
#print axioms DkMath.NumberTheory.GapFocusing.GN_eq_nontrivial_phase_prod
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_eq_geom_sum
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_eq_prod_cyclotomic
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_monic
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_map_rat
#print axioms DkMath.NumberTheory.GapFocusing.cyclotomic_layer_dvd_kernelPolynomial
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_prime
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_eval_zero
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_nonunit_factors
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_mul_degree
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_not_irreducible_mul_degree
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_irreducible_iff_prime
#print axioms DkMath.NumberTheory.GapFocusing.GN_polynomial_rat_irreducible_iff_prime
#print axioms DkMath.NumberTheory.GapFocusing.GN_two
#print axioms DkMath.NumberTheory.GapFocusing.GN_two_mul_degree_p_then_two
#print axioms DkMath.NumberTheory.GapFocusing.GN_two_mul_degree_two_then_p
#print axioms DkMath.NumberTheory.GapFocusing.GN_two_mul_degree_orders
#print axioms DkMath.NumberTheory.GapFocusing.two_mul_prime_divisors_erase_one
#print axioms DkMath.NumberTheory.GapFocusing.kernelPolynomial_two_mul_prime
#print axioms DkMath.NumberTheory.GapFocusing.two_mul_prime_cyclotomic_layer_degrees
#print axioms DkMath.NumberTheory.GapFocusing.phase_geometric_sum_rewrite
#print axioms DkMath.NumberTheory.GapFocusing.phase_geometric_sum_unit
#print axioms DkMath.NumberTheory.GapFocusing.phase_polynomial_associated_iff
#print axioms DkMath.NumberTheory.GapFocusing.unitPowerClass_independent
#print axioms DkMath.NumberTheory.GapFocusing.fixedRamifier_unitPowerClass_independent
#print axioms DkMath.NumberTheory.GapFocusing.sameUnitPowerClass_of_fixed_extraction
#print axioms DkMath.NumberTheory.GapFocusing.ramifier_rescaling
#print axioms DkMath.NumberTheory.GapFocusing.ramifier_rescaling_same_class_iff
#print axioms DkMath.NumberTheory.GapFocusing.ramifier_rescaling_can_change_cube_class
