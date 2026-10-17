import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.ThreeGNSmoke"

example (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN a b c ha hb hc

#check DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv
#check DkMath.FLT.Kummer.exists_cube_eq_stripped_beta
#check DkMath.FLT.Kummer.gnPrimitiveCubicStrictDescent
#check DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN

#print axioms DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN
