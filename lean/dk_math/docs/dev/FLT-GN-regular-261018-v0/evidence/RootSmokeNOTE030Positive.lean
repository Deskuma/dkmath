import DkMath

#print "file: RootSmokeNOTE030Positive"

/-! NOTE-030-004: 通常ルートから正のx付値と同じSourceの下界へ到達する。 -/
#check DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.not_unit_x_of_even_a₂
#check DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.double_x_unit
#check DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.triple_x_valuation_negative
#check DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.nsmul_x_positive_of_prime_order
#check DkMath.FLT.Frey.Source.orbit_x_lower_bound

#print axioms DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.x_positive_of_prime_order
#print axioms DkMath.FLT.Frey.Source.orbit_x_lower_bound

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk36 : k ≤ 36) : 1 ≤ padicValRat 2 (k • Q).xc :=
  S.orbit_x_lower_bound (by decide) (by decide) hbe Q hQp hQ0 k hk1 hk36
