import DkMath

open DkMath.FLT.Kummer.SevenDescent

-- Mathlib's standard statement, independent of any local spelling.
example : _root_.FermatLastTheoremFor 7 := fermatLastTheoremFor_seven

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 7 + b ^ 7 ≠ c ^ 7 := seventh_sum_ne_seventh ha hb hc

#check no_state_one
#check descent_step
#check State.exists_weighted_successor
#check initial_state_of_counterexample

#print axioms fermatLastTheoremFor_seven
