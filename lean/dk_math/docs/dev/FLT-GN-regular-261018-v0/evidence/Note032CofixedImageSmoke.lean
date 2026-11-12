import DkMath.FLT.FreyCofixedImage

#print "file: Note032CofixedImageSmoke"

/-! 005C₁: 同じSource37、同じ核、同じ写像と標的の有理点。商曲線の存在は入力のまま。 -/
namespace Note032CofixedImageSmoke
open Module DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticTorsionRepresentation ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 同じ写像の像の位数37と、その実際の点の固定性を照合する。 -/
theorem source37_image (S : Source 37) (E' : WeierstrassCurve ℚ)
    (φ : Points S.rationalCurve →+ Points E')
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hker : φ.ker = pointSubgroup S.rationalCurve 37 L)
    (hφ : ∀ σ P, φ (pointAction S.rationalCurve σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn S.residualRepresentation L) :
    Nat.card (LinearMap.range (torsionPointMap S.rationalCurve E' 37 φ)) = 37 ∧
      ∀ P : S.ResidualSpace, ∀ σ, pointAction E' σ (φ P.val) = φ P.val :=
  ⟨S.card_residual_pointMap_image E' φ L hline hker,
    cofixed_pointMap_image_fixed S.rationalCurve E' 37 φ L hker hφ hL⟩

/-- 標的の非零有理37捩れ点を得る際にも、元のSourceの点とφの像を保持する。 -/
theorem source37_rational_image (S : Source 37) (E' : WeierstrassCurve ℚ)
    (φ : Points S.rationalCurve →+ Points E')
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hker : φ.ker = pointSubgroup S.rationalCurve 37 L)
    (hφ : ∀ σ P, φ (pointAction S.rationalCurve σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace) (Q : E'.toAffine.Point),
      P ∉ L ∧ 37 • Q = 0 ∧ Q ≠ 0 ∧ baseChangePoint E' Q = φ P.val :=
  S.exists_rational_torsion_of_cofixed_residual_pointMap E' φ L hline hker hφ hL

/-- 商空間の類は、同じ実際の捩れ像へ送られる。抽象的な商を楕円曲線とは呼ばない。 -/
theorem source37_quotient_image (S : Source 37) (E' : WeierstrassCurve ℚ)
    (φ : Points S.rationalCurve →+ Points E') (L : Submodule (ZMod 37) S.ResidualSpace)
    (hker : φ.ker = pointSubgroup S.rationalCurve 37 L) (P : S.ResidualSpace) :
    (CofixedImage.quotientEquivRange (torsionPointMap S.rationalCurve E' 37 φ) L
      (torsionPointMap_ker S.rationalCurve E' 37 φ L hker) (L.mkQ P)).val.val = φ P.val := by
  rw [CofixedImage.quotientEquivRange_apply_val]
  rfl

/-- 005Aの同じE₀[37]との同定を利用し、元の点が同じ零成分の外にあることまで保持する。
零成分の標的への輸送を証明したとはしない。 -/
theorem source37_zeroComponent_outside_image (S : Source 37) (E' : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (φ : Points S.rationalCurve →+ Points E')
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hker : φ.ker = pointSubgroup S.rationalCurve 37 L)
    (hφ : ∀ σ P, φ (pointAction S.rationalCurve σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace) (Q : E'.toAffine.Point),
      P ∉ S.residualZeroComponent A ∧ 37 • Q = 0 ∧ Q ≠ 0 ∧ baseChangePoint E' Q = φ P.val := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hL
  obtain ⟨P, Q, hP, hQ⟩ := S.exists_rational_torsion_of_cofixed_residual_pointMap
    E' φ L hline hker hφ hL
  exact ⟨P, Q, heq ▸ hP, hQ⟩

end Note032CofixedImageSmoke
