import DkMath

#print "file: RootSmokeNOTE010"

/-! NOTE-010: 同じFrey曲線の実際のtorsion・連続作用・Pascal差分へのルート入口。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByAddEquiv
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionContinuousSMul
#check DkMath.FLT.Frey.Source.residualAutomorphisms
#check DkMath.FLT.Frey.Source.residual_underlying
#check DkMath.FLT.Frey.Source.ofCounterexample_residual_entrance
#print axioms DkMath.FLT.Frey.Source.residualRepresentation
#print axioms DkMath.FLT.Frey.Source.residual_action_continuous
#print axioms DkMath.FLT.Frey.Source.ofCounterexample_residual_entrance
#print axioms DkMath.Lib.RepresentationTheory.PascalDifference.end_difference_pow
