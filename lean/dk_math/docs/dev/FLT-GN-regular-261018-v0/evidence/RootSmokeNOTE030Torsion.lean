import DkMath

#print "file: RootSmokeNOTE030Torsion"

/-! NOTE-030-007: 通常ルートから実際の軌道と有理p-torsion排除へ到達する。 -/
#check DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_valuation_spec
#check DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.orbit_conditions
#check DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero
#check DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero
#check DkMath.FLT.Frey.Source.rational_p_torsion_iff

#print axioms DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero
#print axioms DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) : Q = 0 :=
  S.rational_p_torsion_eq_zero (by decide) (by decide) hbe Q hQp

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) : 37 • Q = 0 ↔ Q = 0 :=
  S.rational_p_torsion_iff (by decide) (by decide) hbe Q
