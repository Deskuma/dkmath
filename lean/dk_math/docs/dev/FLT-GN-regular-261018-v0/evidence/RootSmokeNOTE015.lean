import DkMath

#print "file: RootSmokeNOTE015"

/-! NOTE-015: 奇数の正確な点数、次元判定、幾何学から供給した指数2の次元2。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_sum_fibers
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_exists_outside_span
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_root_count
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_two
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two
#check DkMath.FLT.Frey.Source.residual_two_exists_outside_span
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Nat.card (Torsion E 2) = 4 := card_torsion_two E

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Module.finrank (ZMod 2) (Torsion E 2) = 2 :=
  finrank_torsion_two E

example (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : Torsion E 2) (hP : P ≠ 0) :
    ∃ Q : Torsion E 2, Q ∉ Submodule.span (ZMod 2) ({P} : Set (Torsion E 2)) :=
  exists_torsion_two_outside_span E P hP

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Module.finrank (ZMod 37) (Torsion E 37) = 2 ↔ 18 < divisionRootCount E 37 :=
  finrank_torsion_eq_two_iff_root_count E 37 (by decide)

example (S : DkMath.FLT.Frey.Source 37) (h : 37 < Nat.card S.ResidualSpace) :
    Nat.card S.ResidualSpace = 37 ^ 2 := S.residual_card_eq_prime_sq_of_prime_lt h
