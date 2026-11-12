import DkMath

open DkMath.FLT.Kummer

#check DkMath.Lib.NumberTheory.phase_sum_dvd_iff
#check CaseIConjugation.Packet
#check CaseIConjugation.FactorPacketProvider
#check CaseIConjugation.SolutionPacketProvider
#check RegularDescent.Conditions
#check fermatLastTheoremWith_int_of_phase_contracts
#check fermatLastTheoremFor_of_phase_contracts

example : FermatLastTheoremFor 11 := fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := fermatLastTheoremFor_thirteen
example {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 11 + b ^ 11 ≠ c ^ 11 := fermatLastTheoremWith_int_eleven a b c ha hb hc
example {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 13 + b ^ 13 ≠ c ^ 13 := fermatLastTheoremWith_int_thirteen a b c ha hb hc

#print axioms fermatLastTheoremWith_int_of_phase_contracts
#print axioms classical_solution_packet_provider
#print axioms regular_prime_conditions
#print axioms fermatLastTheoremFor_eleven
#print axioms fermatLastTheoremFor_thirteen
