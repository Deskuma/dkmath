import DkMath.FLT.FreyFiniteKernelNonsingular

#print "file: Note032TargetNonsingularSmoke"

/-! 同じSource37・同じ直線について、標的楕円性・全点関数・零ファイバーの追加providerを除去する。 -/
namespace Note032TargetNonsingularSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource37の標的判別式非零。三値分離・標的楕円性の仮定はない。 -/
theorem source37_discriminant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) : (S.residualKernelModel L hline).Δ ≠ 0 :=
  S.residual_kernel_model_discriminant_ne_zero (by decide) L hline

/-- 同じ標的のIsEllipticを内部供給できる。 -/
theorem source37_elliptic (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) : (S.residualKernelModel L hline).IsElliptic :=
  S.residual_kernel_model_isElliptic (by decide) L hline

/-- 同じ核の外の全実点が、同じ標的の非特異点へ移る。 -/
theorem source37_nonsingular (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve 37 L) :
    (S.residualKernelModel L hline).toAffine.Nonsingular
      (S.residualKernelXAt L hline P hP) (S.residualKernelYAt L hline P hP) :=
  S.residual_kernel_at_nonsingular (by decide) L hline P hP

/-- 全点関数の正確な零ファイバー。標的IsEllipticインスタンスを引数に持たない。 -/
theorem source37_zero_fiber (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve) :
    S.residualOddKernelPointMap (by decide) L hline P = 0 ↔ P ∈ pointSubgroup S.rationalCurve 37 L :=
  S.residual_odd_kernel_pointMap_eq_zero_iff (by decide) L hline P

/-- 同じ直線が安定なら、同じ標的に基底変換で等しいℚ係数楕円曲線を得る。 -/
theorem source37_rational_elliptic (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hstable : IsStable S.residualRepresentation L) :
    ∃ W : WeierstrassCurve ℚ, W.map (algebraMap ℚ (AlgebraicClosure ℚ)) = S.residualKernelModel L hline ∧
      W.IsElliptic ∧ W.a₁ = S.rationalCurve.a₁ ∧ W.a₃ = S.rationalCurve.a₃ :=
  S.exists_rational_elliptic_residual_kernel_model (by decide) L hline hstable

end Note032TargetNonsingularSmoke
