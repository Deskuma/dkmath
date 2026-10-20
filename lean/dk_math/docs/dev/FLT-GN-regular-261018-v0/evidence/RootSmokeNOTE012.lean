import DkMath

#print "file: RootSmokeNOTE012"

/-! NOTE-012: 標数0の実際のtorsionの有限性と、位数入力を持たないFrey有限レベル。 -/
#check DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionFinite
#check DkMath.FLT.Frey.Source.residual_finite_of_ne_zero
#check DkMath.FLT.Frey.Source.residualKernel_isOpen_of_prime
#check DkMath.FLT.Frey.Source.residual_normal_finite_level
#check DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero
#print axioms DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

example (E : WeierstrassCurve ℚ) : Finite (Torsion E 37) := inferInstance

example (E : WeierstrassCurve ℚ) : FactorsThroughFiniteLevel E 37 :=
  factorsThroughFiniteLevel_of_ne_zero E 37 (by decide)
