import DkMath

#print "file: RootSmokeNOTE030"

/-! NOTE-030-001〜003: 通常ルートから同じSource・実際の点の付値へ到達する。 -/
#check DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_lower
#check DkMath.Lib.Algebra.FiniteOrbitMinimum.nsmul_nonnegative_of_double_drop
#check DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.double_x_valuation_drop
#check DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order
#check DkMath.FLT.Frey.Source.a₂_twoAdic_integral
#check DkMath.FLT.Frey.Source.a₄_twoAdic_exact
#check DkMath.FLT.Frey.Source.x_nonnegative_of_prime_torsion

#print axioms DkMath.FLT.Frey.Source.a₂_twoAdic_integral
#print axioms DkMath.FLT.Frey.Source.x_nonnegative_of_prime_torsion

open DkMath.FLT.Frey

example (S : Source 37) (hbe : Even S.b) :
    DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact S.twoAdicGamma S.rationalCurve.a₄ :=
  S.a₄_twoAdic_exact hbe

example (S : Source 37) (hbe : Even S.b) (Q : S.rationalCurve.toAffine.Point)
    (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0) (k : ℕ) :
    0 ≤ padicValRat 2 (k • Q).xc :=
  S.x_nonnegative_of_prime_torsion (by decide) (by decide) hbe Q hQp hQ0 k
