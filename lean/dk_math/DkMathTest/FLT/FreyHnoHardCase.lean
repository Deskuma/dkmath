/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoHardCase
import DkMath.FLT.FreyTorsionTowerObstruction

namespace DkMathTest.FLT.FreyHnoHardCase

open DkMath.FLT.Frey DkMath.FLT.Frey.Source

-- All four completed FLT endpoints reach the signed-integer Source type.
-- These are upper-layer consumers of FLT, not a new proof of those FLTs.
example : IsEmpty (Source 5) := ⟨fun S => S.false_of_small_prime_index (by simp)⟩
example : IsEmpty (Source 7) := ⟨fun S => S.false_of_small_prime_index (by simp)⟩
example : IsEmpty (Source 11) := ⟨fun S => S.false_of_small_prime_index (by simp)⟩
example : IsEmpty (Source 13) := ⟨fun S => S.false_of_small_prime_index (by simp)⟩

#check ofCounterexample_hard_case_of_cofixed
#check residual_hno_iff_no_hard_case
#check residual_cofixed_line_forces_irregular_hard_case
#check residual_line_tower_frobenius_impossible

#print axioms DkMath.FLT.Five.fermatLastTheoremFor_five
#print axioms false_of_small_prime_index
#print axioms seventeen_le_of_five_le
#print axioms false_of_regular_prime
#print axioms residual_hno_of_regular_prime
#print axioms prime_dvd_cyclotomic_classGroup_card
#print axioms residual_cofixed_line_forces_irregular_hard_case
#print axioms residual_hno_of_small_prime_index
#print axioms residual_cofixed_line_forces_hard_case
#print axioms residual_hno_iff_no_hard_case
#print axioms residual_hno_iff_no_irregular_hard_case
#print axioms ofCounterexample_hard_case_of_cofixed
#print axioms residual_line_tower_scalar_absorption_impossible
#print axioms residual_line_tower_frobenius_impossible

end DkMathTest.FLT.FreyHnoHardCase
