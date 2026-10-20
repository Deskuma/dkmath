import DkMath

#print "file: RootSmokeNOTE013"

/-! NOTE-013: 正確な位数公式を使わない次元上界と、同じFrey Sourceへの接続。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_le_two
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_degree_bound
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_le_two
#check DkMath.FLT.Frey.Source.residual_bounded_profile
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two
#print axioms DkMath.FLT.Frey.Source.residual_bounded_profile

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) : Module.finrank (ZMod 37) (Torsion E 37) ≤ 2 :=
  finrank_torsion_le_two E 37

example (E : WeierstrassCurve ℚ) : Nat.card (Torsion E 37) ≤ 1369 :=
  card_torsion_le_prime_sq E 37

example (S : DkMath.FLT.Frey.Source 37) :
    Module.finrank (ZMod 37) S.ResidualSpace ≤ 2 ∧
      Nat.card S.ResidualSpace ≤ 37 ^ 2 ∧ S.ResidualFactorsThroughFiniteLevel :=
  S.residual_bounded_profile
