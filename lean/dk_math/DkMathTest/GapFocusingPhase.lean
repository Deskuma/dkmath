/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.Phase

#print "file: DkMathTest.GapFocusingPhase"

/-! Durable type and dependency audit for the split cyclotomic phase API. -/

open DkMath.NumberTheory.GapFocusing

#check phaseFactor_eq_gap_forall_iff
#check phaseFactor_polynomial_eq_gap_iff
#check focused_pow_sub_pow_eq_prod
#check focused_pow_sub_pow_eq_prod_range
#check focused_pow_sub_pow_eq_prod_fin
#check indexed_phase_eq_gap_forall_iff
#check phaseFactor_eq_gap_iff_of_ne_zero
#check GN_eq_nontrivial_phase_prod_range
#check GN_eq_nontrivial_phase_prod

#print axioms phaseFactor_eq_gap_forall_iff
#print axioms phaseFactor_polynomial_eq_gap_iff
#print axioms focused_pow_sub_pow_eq_prod
#print axioms focused_pow_sub_pow_eq_prod_range
#print axioms focused_pow_sub_pow_eq_prod_fin
#print axioms indexed_phase_eq_gap_forall_iff
#print axioms phaseFactor_eq_gap_iff_of_ne_zero
#print axioms GN_eq_nontrivial_phase_prod_range
#print axioms GN_eq_nontrivial_phase_prod
