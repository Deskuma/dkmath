import DkMath

#print "file: RootSmokeNOTE031UnramifiedAway"

/-! NOTE-031-002: 通常ルートから全倍点の深さとq≠2,pの最終固定性へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add
#check DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_pair_smooth
#check DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves
#check DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth
#check DkMath.Lib.NumberTheory.EllipticDepthInertia.finite_point_fixed_of_rational_depth
#check @DkMath.FLT.Frey.Source.residual_fixed_at_bad_prime 37
#check @DkMath.FLT.Frey.Source.residual_fixed_away_two_self 37
#check @DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self 37
#print axioms DkMath.FLT.Frey.Source.residual_fixed_away_two_self
#print axioms DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self
