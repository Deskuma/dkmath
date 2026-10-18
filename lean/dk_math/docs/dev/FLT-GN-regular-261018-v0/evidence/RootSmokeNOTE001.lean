import DkMath

open DkMath.FLT.Kummer

#check DkMath.Lib.NumberTheory.phase_sum_dvd_iff
#check DkMath.Lib.NumberTheory.four_phase_obstruction
#check first_case_conjugation_packet
#check not_int_solution_caseI
#check positive_state_of_second_case
#check fermatLastTheoremFor_of_regular_prime

example : FermatLastTheoremFor 11 := fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := fermatLastTheoremFor_thirteen
example : FermatLastTheoremWith ℤ 11 := fermatLastTheoremWith_int_eleven
example : FermatLastTheoremWith ℤ 13 := fermatLastTheoremWith_int_thirteen

#print axioms DkMath.Lib.NumberTheory.phase_sum_dvd_iff
#print axioms not_int_solution_caseI
#print axioms fermatLastTheoremFor_of_regular_prime
#print axioms fermatLastTheoremFor_eleven
#print axioms fermatLastTheoremFor_thirteen
