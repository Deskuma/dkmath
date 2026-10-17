import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.FiveGNSmoke"

example (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 :=
  DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN a b c ha hb hc

#check DkMath.Lib.NumberTheory.quinticGoldenEquiv
#check DkMath.Lib.NumberTheory.quinticGoldenNorm_eq_algebraNorm
#check DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion
#check DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN
#check DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN
#print axioms DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN
