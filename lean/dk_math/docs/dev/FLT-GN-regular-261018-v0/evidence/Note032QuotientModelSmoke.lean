import DkMath.FLT.FreyFiniteKernelModel

#print "file: Note032QuotientModelSmoke"

/-! 同じSource37からの三次モデル、実際の関数体単射、像・次数37、安定直線の係数降下。
Sourceや安定直線の存在、標的楕円性、isogeny、零成分輸送を結論しない。 -/
namespace Note032QuotientModelSmoke
open Polynomial IntermediateField Module WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticFiniteKernel EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ二関数が同じ三次モデルの方程式を満たす。 -/
theorem source37_equation (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    ((S.residualKernelModel L hline).toAffine⁄
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
        (S.residualKernelX L hline) (S.residualKernelY L hline) :=
  S.residual_kernel_model_equation L hline

/-- 同じ一般点が非特異。Δ≠0をこの命題へ混ぜない。 -/
theorem source37_generic_nonsingular (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    ((S.residualKernelModel L hline).toAffine⁄
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Nonsingular
        (S.residualKernelX L hline) (S.residualKernelY L hline) :=
  S.residual_kernel_model_generic_nonsingular L hline

/-- 引き戻しは実際の単射で、像は同じ残余実点核の固定体。 -/
theorem source37_pull (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    Function.Injective (S.residualKernelModelPull L hline) ∧
    (S.residualKernelModelPull L hline).fieldRange =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L) :=
  ⟨(S.residualKernelModelPull L hline).injective, S.residual_kernel_model_fieldRange L hline⟩

/-- 数値次数37を外部入力なしで内部供給する。 -/
theorem source37_degree (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    Module.finrank (S.residualKernelModelPull L hline).fieldRange
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 37 :=
  S.finrank_residual_kernel_model_pull L hline

/-- 同じ安定直線のモデルをℚ係数へ降下する。直線の存在自体は入力のまま。 -/
theorem source37_rational_model (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (hstable : IsStable S.residualRepresentation L) :
    ∃ W : WeierstrassCurve ℚ,
      W.map (algebraMap ℚ (AlgebraicClosure ℚ)) = S.residualKernelModel L hline ∧
      W.a₁ = S.rationalCurve.a₁ ∧ W.a₃ = S.rationalCurve.a₃ :=
  S.exists_rational_residual_kernel_model L hline hstable

end Note032QuotientModelSmoke
