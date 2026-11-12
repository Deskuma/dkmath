import DkMath

#print "file: RootSmokeNOTE014"

/-! NOTE-014: 楕円曲線性から実際の非零点を構成し、次元0を除く公開入口。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_affine_equation_y
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_iff_coordinate_root
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_bounds
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_or_prime_sq
#check DkMath.FLT.Frey.Source.residual_nontrivial_profile
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt
#print axioms DkMath.FLT.Frey.Source.residual_nontrivial_profile

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Nontrivial (Torsion E 37) := inferInstance

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : ∃ P : Torsion E 4, P ≠ 0 :=
  exists_nonzero_torsion_of_one_lt E 4 (by decide)

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    1 ≤ Module.finrank (ZMod 37) (Torsion E 37) ∧
      Module.finrank (ZMod 37) (Torsion E 37) ≤ 2 :=
  finrank_torsion_bounds E 37

example (S : DkMath.FLT.Frey.Source 37) :
    (1 ≤ Module.finrank (ZMod 37) S.ResidualSpace ∧
      Module.finrank (ZMod 37) S.ResidualSpace ≤ 2) ∧
      (37 ≤ Nat.card S.ResidualSpace ∧ Nat.card S.ResidualSpace ≤ 37 ^ 2) ∧
      S.ResidualFactorsThroughFiniteLevel :=
  S.residual_nontrivial_profile
