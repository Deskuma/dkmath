import DkMath

#print "file: RootSmokeNOTE030Bounds"

/-! NOTE-030-005: 通常ルートから反射と同じSourceの上下界へ到達する。 -/
#check DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_x
#check DkMath.Lib.NumberTheory.WeierstrassXReflection.double_add_twoTorsionPoint
#check DkMath.Lib.NumberTheory.WeierstrassXReflection.odd_nsmul_add_twoTorsionPoint
#check DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order
#check DkMath.FLT.Frey.Source.orbit_x_bounds

#print axioms DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order
#print axioms DkMath.FLT.Frey.Source.orbit_x_bounds

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk36 : k ≤ 36) :
    1 ≤ padicValRat 2 (k • Q).xc ∧ padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma - 1 :=
  S.orbit_x_bounds (by decide) (by decide) hbe Q hQp hQ0 k hk1 hk36
