import DkMath

#print "file: RootSmokeNOTE030Identities"

/-! NOTE-030-006: 通常ルートから分母のExactと倍点・和差の付値等式へ到達する。 -/
#check DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_polynomial_identity
#check DkMath.Lib.NumberTheory.WeierstrassXIdentities.tangent_denominator_exact
#check DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order
#check DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order
#check DkMath.FLT.Frey.Source.tangent_denominator_exact_of_prime_torsion

#print axioms DkMath.FLT.Frey.Source.double_x_valuation_identity
#print axioms DkMath.FLT.Frey.Source.plus_minus_x_valuation_identity

example (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0) :
    Q.xc ^ 2 - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 (2 • Q).xc + 2 * padicValRat 2 Q.xc =
      2 * padicValRat 2 (Q.xc ^ 2 - S.rationalCurve.a₄) :=
  S.double_x_valuation_identity (by decide) (by decide) hbe Q hQp hQ0

example (S : DkMath.FLT.Frey.Source 37)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk2 : 2 ≤ k) (hk35 : k ≤ 35) :
    (k • Q).xc ≠ Q.xc ∧ (k • Q).xc * Q.xc - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 ((k + 1) • Q).xc + padicValRat 2 ((k - 1) • Q).xc +
      2 * padicValRat 2 ((k • Q).xc - Q.xc) =
      2 * padicValRat 2 ((k • Q).xc * Q.xc - S.rationalCurve.a₄) :=
  S.plus_minus_x_valuation_identity (by decide) (by decide) Q hQp hQ0 k hk2 hk35
