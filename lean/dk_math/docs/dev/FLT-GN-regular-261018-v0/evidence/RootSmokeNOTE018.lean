import DkMath

#print "file: RootSmokeNOTE018"

/-! NOTE-018: 無条件の円分指標・倍写像全射性と、Weil対を明示入力する行列式の接続。 -/
#check DkMath.Lib.RepresentationTheory.alternating_map_eq_det_smul
#check DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing
#check DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData
#check DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic_of_pairing
#check DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product_of_pairing
#print axioms DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing
#print axioms DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic_of_pairing
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example : Nat.card (rootsOfUnity 37 (AlgebraicClosure ℚ)) = 37 := prime_root_card 37

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Surjective (nsmulAddMonoidHom 4 : Points E →+ Points E) :=
  multiplication_surjective E 4 (by decide)

example (E : WeierstrassCurve ℚ) [E.IsElliptic] (w : WeilPairingData E 37)
    (σ : Field.absoluteGaloisGroup ℚ) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ 37 = 1) :
    σ.toAlgHom ζ = ζ ^ (LinearMap.det (representation E 37 σ)).val :=
  torsion_apply_eq_pow_det_of_pairing E 37 w σ ζ hζ

example (S : DkMath.FLT.Frey.Source 37) (w : S.ResidualWeilPairingData) :
    S.residualDeterminantCharacter = cyclotomicCharacter 37 :=
  S.residual_determinant_eq_cyclotomic_of_pairing w
