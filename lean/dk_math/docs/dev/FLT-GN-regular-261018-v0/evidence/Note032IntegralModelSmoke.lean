import DkMath.FLT.FreyFiniteKernelIntegralModel

#print "file: Note032IntegralModelSmoke"

/-! 同じSource37・残余直線・既存標的の整数モデルと、同じ実点準同型の接続。 -/
namespace Note032IntegralModelSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じSource37の整数係数標的の判別式は非零。 -/
theorem source37_integer_discriminant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    (S.residualIntegerKernelModel L hl hs).Δ ≠ 0 :=
  S.residual_integer_kernel_model_discriminant_ne_zero (by decide) L hl hs

/-- 整数標的への同じ準同型も、正確に同じHを核に持つ。 -/
theorem source37_integer_kernel (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    (S.residualIntegerKernelPointHom (by decide) L hl hs).ker = pointSubgroup S.rationalCurve 37 L :=
  S.residual_integer_kernel_pointHom_ker (by decide) L hl hs

/-- 同じ整数標的の幾何学的点への全射性。 -/
theorem source37_integer_surjective (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    Function.Surjective (S.residualIntegerKernelPointHom (by decide) L hl hs) :=
  S.residual_integer_kernel_pointHom_surjective (by decide) L hl hs

/-- 同じ整数標的への準同型はGalois同変である。 -/
theorem source37_integer_equivariant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualIntegerKernelPointHom (by decide) L hl hs (pointAction S.rationalCurve σ P) =
      pointAction ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) σ
        (S.residualIntegerKernelPointHom (by decide) L hl hs P) :=
  S.residual_integer_kernel_pointHom_equivariant (by decide) L hl hs σ P

/-- Cofixedなら、同じ整数モデルに非零有理37捩れ点が存在する。 -/
theorem source37_integer_rational_torsion (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : ((S.residualIntegerKernelModel L hl hL.isStable).map (Int.castRingHom ℚ)).toAffine.Point),
      P ∉ L ∧ 37 • R = 0 ∧ R ≠ 0 ∧
        baseChangePoint _ R = S.residualIntegerKernelPointHom (by decide) L hl hL.isStable P.val :=
  S.exists_rational_torsion_on_integer_kernel (by decide) L hl hL

end Note032IntegralModelSmoke
