import DkMath.FLT.FreyFiniteKernelPointDescent

#print "file: Note032PointDescentSmoke"

/-! 同じSource37・同じ安定直線の降下全点関数とCofixed有理像を検査する。 -/
namespace Note032PointDescentSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ安定直線の選択済みℚ係数モデルの楕円性。 -/
theorem source37_target (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    (S.residualDescendedKernelModel L hline hs).IsElliptic :=
  S.residual_descended_kernel_model_isElliptic (by decide) L hline hs

/-- 前回の同じ全点関数への接続。存在するだけの別写像へ置換しない。 -/
theorem source37_same_map (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (P : Points S.rationalCurve) :
    pointModelEquiv (S.residual_descended_kernel_model_map L hline hs)
      (S.residualDescendedKernelPointMap (by decide) L hline hs P) =
        S.residualOddKernelPointMap (by decide) L hline P :=
  S.residual_descended_kernel_pointMap_transport (by decide) L hline hs P

/-- 降下後の同じ全点関数の零ファイバー。 -/
theorem source37_zero_fiber (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointMap (by decide) L hline hs P = 0 ↔
      P ∈ pointSubgroup S.rationalCurve 37 L :=
  S.residual_descended_kernel_pointMap_eq_zero_iff (by decide) L hline hs P

/-- 実際の標準Galois作用との可換性をproviderなしで利用できる。 -/
theorem source37_equivariant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointMap (by decide) L hline hs (pointAction S.rationalCurve σ P) =
      pointAction (S.residualDescendedKernelModel L hline hs) σ
        (S.residualDescendedKernelPointMap (by decide) L hline hs P) :=
  S.residual_descended_kernel_pointMap_equivariant (by decide) L hline hs σ P

/-- Cofixedなら非零有理像を同じ曲線上に構成。37捩れ性の結論は含まない。 -/
theorem source37_nonzero_rational_image (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : (S.residualDescendedKernelModel L hline hL.isStable).toAffine.Point),
      P ∉ L ∧ R ≠ 0 ∧ baseChangePoint _ R =
        S.residualDescendedKernelPointMap (by decide) L hline hL.isStable P.val :=
  S.exists_nonzero_rational_residual_kernel_image (by decide) L hline hL

end Note032PointDescentSmoke
