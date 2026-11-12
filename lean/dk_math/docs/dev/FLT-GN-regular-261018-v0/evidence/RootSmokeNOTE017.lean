import DkMath

#print "file: RootSmokeNOTE017"

/-! NOTE-017: 同じ実際の点の表現をGL₂へ運び、既存の既約性と安定直線の条件を照合する。 -/
#check DkMath.Lib.RepresentationTheory.matrixGroupHom_basis_change
#check DkMath.Lib.RepresentationTheory.matrixGroupHom_charpoly_basis_independent
#check DkMath.Lib.RepresentationTheory.determinantCharacterWithBasis_independent
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2
#check DkMath.FLT.Frey.Source.residualGL2
#check DkMath.FLT.Frey.Source.residual_gl2_profile
#print axioms DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line
#print axioms DkMath.FLT.Frey.Source.residual_isIrreducible_iff_no_stable_line
#print axioms DkMath.FLT.Frey.Source.residual_gl2_profile

noncomputable section

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Field.absoluteGaloisGroup ℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 37) := torsionGL2 E 37

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionGL2 E 37).ker = representationKernel E 37 := torsionGL2_ker E 37

example (S : DkMath.FLT.Frey.Source 37) :
    S.ResidualIsIrreducible ↔ ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace,
      Module.finrank (ZMod 37) L = 1 ∧ S.IsGaloisStable L :=
  S.residual_isIrreducible_iff_no_stable_line

example (S : DkMath.FLT.Frey.Source 37) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ Normal ℚ L ∧
      L.fixingSubgroup ≤ S.residualGL2.ker := S.residualGL2_normal_finite_level
