import DkMath

#print "file: RootSmokeNOTE016"

/-! NOTE-016: 実際の正則ファイバーの根から核へ、位数・次元の追加入力なしで接続する。 -/
#check DkMath.Lib.Algebra.RationalPolynomialFiber.finite_not_separable_fiber
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_isCoprime
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_wronskian_ne_zero
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRootEmbedding
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime
#check DkMath.FLT.Frey.Source.residual_rank_two_profile
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Nat.card (Torsion E 37) = 1369 :=
  card_torsion_prime_sq E 37

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Module.finrank (ZMod 37) (Torsion E 37) = 2 :=
  finrank_torsion_prime E 37

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : divisionRootCount E 37 = 684 :=
  divisionRootCount_odd_prime E 37 (by decide)

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : 16 ≤ Nat.card (Torsion E 4) :=
  square_le_card_torsion E 4 (by decide)

example (S : DkMath.FLT.Frey.Source 37) :
    Nat.card S.ResidualSpace = 37 ^ 2 ∧ Module.finrank (ZMod 37) S.ResidualSpace = 2 ∧
      S.ResidualFactorsThroughFiniteLevel := S.residual_rank_two_profile
