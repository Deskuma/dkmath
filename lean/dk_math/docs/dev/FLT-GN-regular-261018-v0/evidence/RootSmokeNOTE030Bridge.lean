import DkMath

#print "file: RootSmokeNOTE030Bridge"

/-! NOTE-030-008: 通常ルートから同じSourceの固定点消滅とhrat供給済み入口へ到達する。 -/
#check DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented
#check DkMath.FLT.Frey.Source.residual_fixed_eq_zero_of_oriented
#check DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_oriented
#check DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_no_cofixed_line
#check DkMath.FLT.Frey.Source.ofCounterexample_residual_noNonzeroFixed

#print axioms DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented
#print axioms DkMath.FLT.Frey.Source.ofCounterexample_residual_noNonzeroFixed

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b) :
    DkMath.Lib.RepresentationTheory.NoNonzeroFixed S.residualRepresentation :=
  S.residual_noNonzeroFixed_of_oriented (by decide) (by decide) hbe

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (P : S.ResidualSpace) (hP : ∀ σ, S.residualRepresentation σ P = P) : P = 0 :=
  S.residual_fixed_eq_zero_of_oriented (by decide) (by decide) hbe P hP
