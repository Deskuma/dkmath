import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example : sevenAxisDepth (cyclotomicSevenToTraceOne 8 1) = 1 := by
  apply sevenAxisDepth_cyclotomicSeven_eq_one
  · norm_num
  · norm_num

example : sevenAxisDepth (cyclotomicSevenToTraceOne 50 1) = 1 := by
  apply sevenAxisDepth_cyclotomicSeven_eq_one
  · norm_num
  · norm_num

example : sevenAxisDepth (cyclotomicSevenToTraceOne 2 1) = 0 := by
  apply sevenAxisDepth_cyclotomicSeven_eq_zero
  · norm_num
  · norm_num

example : padicValNat 7 (GN 7 (50 - 1) 1) = 1 := by
  rw [padicValNat_GN_seven_sub_eq_if (a := 50) (b := 1) (by omega) (by norm_num)]
  norm_num

example : ¬ 49 ∣ GN 7 (50 - 1) 1 := by
  exact not_fortyNine_dvd_GN_seven_sub (a := 50) (b := 1)
    (by omega) (by norm_num) (by norm_num)

example :
    ∃ r : TraceOneInt (-2),
      cyclotomicSevenToTraceOne 8 1 = sevenAxis * r ∧
      r ≠ 0 ∧ ¬ sevenAxis ∣ r ∧ ¬ (7 : ℤ) ∣ norm r ∧
      cyclotomicSeven 8 1 = 7 * norm r ∧ 1 ≤ norm r := by
  apply exists_cyclotomicSeven_terminal_core
  · norm_num
  · norm_num

#print axioms cyclotomicSeven_substitution_expansion
#print axioms fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow
#print axioms not_fortyNine_dvd_cyclotomicSeven
#print axioms sevenAxisDepth_cyclotomicSeven_eq_one
#print axioms sevenAxisDepth_cyclotomicSeven_eq_zero
#print axioms sevenAxisDepth_cyclotomicSeven_eq_if
#print axioms exists_cyclotomicSeven_terminal_core
#print axioms not_seven_dvd_right_of_coprime_of_seven_dvd_sub
#print axioms sevenAxisDepth_cyclotomicSeven_nat_eq_one
#print axioms padicValNat_GN_seven_sub_eq_if
#print axioms padicValNat_GN_seven_sub_le_one
#print axioms padicValNat_GN_seven_sub_eq_one_iff
#print axioms not_fortyNine_dvd_GN_seven_sub
