import DkMath.FLT.FreyCofixedCyclotomic

#print "file: Note032CofixedCyclotomicSmoke"

/-! 032-005B: 指数37の同じSourceと実点で行列式・円分スカラー・倍点を照合する。 -/
namespace Note032CofixedCyclotomicSmoke
open Module DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticTorsionRepresentation CyclotomicRootModule ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 行列式倍、円分倍、実際の点群の倍点は同じPへの作用である。
Cofixed直線の存在は仮定のまま保持する。 -/
theorem source37_same_line_action (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ L) :
    S.residualRepresentation σ P = LinearMap.det (S.residualRepresentation σ) • P ∧
      S.residualRepresentation σ P = (cyclotomicCharacter 37 σ : ZMod 37) • P ∧
      pointAction S.rationalCurve σ P.val = (cyclotomicCharacter 37 σ : ZMod 37).val • P.val :=
  ⟨S.residual_cofixed_line_apply_eq_det_smul L hline hcofixed σ hP,
    S.residual_cofixed_line_apply_eq_cyclotomic_smul L hline hcofixed σ hP,
    S.residual_cofixed_line_pointAction_eq_cyclotomic_nsmul L hline hcofixed σ hP⟩

/-- 核候補の同じ実点Qに、同じ円分倍点公式を供給する。商曲線は仮定しない。 -/
theorem source37_point_subgroup_action (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {Q : Points S.rationalCurve}
    (hQ : Q ∈ pointSubgroup S.rationalCurve 37 L) :
    pointAction S.rationalCurve σ Q = (cyclotomicCharacter 37 σ : ZMod 37).val • Q :=
  S.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul L hline hcofixed σ hQ

/-- 適合基底の右上成分を保持した、同じGL₂行列の形。 -/
theorem source37_adapted_matrix (S : Source 37) (b : Basis (Fin 2) (ZMod 37) S.ResidualSpace)
    (hcofixed : IsCofixedOn S.residualRepresentation
      (Submodule.span (ZMod 37) ({b 0} : Set S.ResidualSpace)))
    (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod 37)) =
      !![(cyclotomicCharacter 37 σ : ZMod 37),
        (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod 37)) 0 1; 0, 1] :=
  S.residual_cofixed_basis_matrix b hcofixed σ

/-- 005Aの候補同定を介し、同じE₀[37]へ円分作用を運ぶ。
大域Cofixed性は入力であり、7側の局所条件だけへ弱めない。 -/
theorem source37_zeroComponent_action (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ S.residualZeroComponent A) :
    S.residualRepresentation σ P = (cyclotomicCharacter 37 σ : ZMod 37) • P :=
  S.residualZeroComponent_apply_eq_cyclotomic_smul_of_cofixed_line (by decide) A hA L hline hcofixed σ hP

end Note032CofixedCyclotomicSmoke
