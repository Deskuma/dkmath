import DkMath.FLT.FreyFiniteKernelHom

#print "file: Note032AbelHomSmoke"

/-! 同じSource37・残余直線・標的について、加法性から実際の有理37捩れ像まで接続する。 -/
namespace Note032AbelHomSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じSource37の既存全点関数の加法性。 -/
theorem source37_additivity (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P Q : Points S.rationalCurve) :
    S.residualOddKernelPointMap (by decide) L hline (P + Q) =
      S.residualOddKernelPointMap (by decide) L hline P + S.residualOddKernelPointMap (by decide) L hline Q :=
  (S.residualOddKernelPointHom (by decide) L hline).map_add P Q

/-- 同じSource37の実点準同型の核は、同じLの実点核Hである。 -/
theorem source37_kernel (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) :
    (S.residualOddKernelPointHom (by decide) L hline).ker = pointSubgroup S.rationalCurve 37 L :=
  S.residual_odd_kernel_pointHom_ker (by decide) L hline

/-- 同じℚモデル上の準同型は標準Galois作用と可換である。 -/
theorem source37_equivariant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointHom (by decide) L hline hs (pointAction S.rationalCurve σ P) =
      pointAction (S.residualDescendedKernelModel L hline hs) σ
        (S.residualDescendedKernelPointHom (by decide) L hline hs P) :=
  S.residual_descended_kernel_pointHom_equivariant (by decide) L hline hs σ P

/-- 同じ構成済み準同型の37捩れ像の位数は37。 -/
theorem source37_torsion_image_card (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    Nat.card (LinearMap.range (torsionPointMap S.rationalCurve
      (S.residualDescendedKernelModel L hline hs) 37 (S.residualDescendedKernelPointHom (by decide) L hline hs))) = 37 :=
  S.card_residual_kernel_torsion_image (by decide) L hline hs

/-- Cofixed直線があれば、同じℚ係数標的に非零有理37捩れ点が実際に得られる。 -/
theorem source37_rational_torsion (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : (S.residualDescendedKernelModel L hline hL.isStable).toAffine.Point),
      P ∉ L ∧ 37 • R = 0 ∧ R ≠ 0 ∧
        baseChangePoint _ R = S.residualDescendedKernelPointMap (by decide) L hline hL.isStable P.val :=
  S.exists_rational_torsion_of_cofixed_kernel (by decide) L hline hL

end Note032AbelHomSmoke
