/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGlobal
import DkMath.FLT.FreyCofixedImage
import DkMath.Lib.NumberTheory.EllipticFiniteKernelHom

#print "file: DkMath.FLT.FreyFiniteKernelHom"

/-!
# 同じFrey Sourceの実点準同型と、Cofixed核からの有理p捩れ

同じ残余直線L、実点核H、既存の商座標・降下モデルを全て保持する。
主因子輸送とアフィンAbel対応から、既存の同じ点関数の加法性を内部供給する。
同じ準同型の核はH、標準Galois作用と可換であり、p捩れ像は位数pとなる。
Cofixedなら同じℚ係数標的に実際の非零有理p捩れ点を得る。

標的は元のSourceの曲線とは異なる。元のSourceに証明した有理捩れ排除は流用しない。
標的の整数モデル・局所還元・零成分輸送と一般hnoは、引き続き別の数学的課題である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelHom {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceの既存全点関数を、そのまま加法準同型へ昇格する。 -/
noncomputable def residualOddKernelPointHom (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Points S.rationalCurve →+ (S.residualKernelModel L hline).toAffine.Point := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointHom S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)

/-- 同じSourceの新しい準同型の値は、既存の同じ全点関数の値である。 -/
theorem residualOddKernelPointHom_apply (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) :
    S.residualOddKernelPointHom hp2 L hline P = S.residualOddKernelPointMap hp2 L hline P := rfl

/-- 同じSource・同じ直線の零ファイバーは、実際の準同型の核として同じHとなる。 -/
theorem residual_odd_kernel_pointHom_ker (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (S.residualOddKernelPointHom hp2 L hline).ker = pointSubgroup S.rationalCurve p L := by
  ext P
  exact S.residual_odd_kernel_pointMap_eq_zero_iff hp2 L hline P

/-- 同じ実点準同型は全射である。 -/
theorem residual_odd_kernel_pointHom_surjective (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Function.Surjective (S.residualOddKernelPointHom hp2 L hline) :=
  S.residual_odd_kernel_pointMap_surjective hp2 L hline

/-- 同じ安定直線の既存ℚ係数モデルへ降りる実点加法準同型。 -/
noncomputable def residualDescendedKernelPointHom (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Points S.rationalCurve →+ Points (S.residualDescendedKernelModel L hline hstable) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelPointHom S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)
    (pointSubgroup_stable S.rationalCurve p L hstable)

/-- ℚモデルへの準同型も、既存の同じ降下点関数を保持する。 -/
theorem residualDescendedKernelPointHom_apply (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointHom hp2 L hline hstable P =
      S.residualDescendedKernelPointMap hp2 L hline hstable P := rfl

/-- 同じ降下準同型の核は、同じ残余直線の実点核Hに正確に一致する。 -/
theorem residual_descended_kernel_pointHom_ker (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualDescendedKernelPointHom hp2 L hline hstable).ker = pointSubgroup S.rationalCurve p L := by
  ext P
  exact S.residual_descended_kernel_pointMap_eq_zero_iff hp2 L hline hstable P

/-- 同じ降下準同型の標準実点Galois作用との同変性。 -/
theorem residual_descended_kernel_pointHom_equivariant (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointHom hp2 L hline hstable (pointAction S.rationalCurve σ P) =
      pointAction (S.residualDescendedKernelModel L hline hstable) σ
        (S.residualDescendedKernelPointHom hp2 L hline hstable P) :=
  S.residual_descended_kernel_pointMap_equivariant hp2 L hline hstable σ P

/-- 同じ構成済み準同型のp捩れ像の位数はp。写像や核を外部入力にしない。 -/
theorem card_residual_kernel_torsion_image (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Nat.card (LinearMap.range (torsionPointMap S.rationalCurve
      (S.residualDescendedKernelModel L hline hstable) p
      (S.residualDescendedKernelPointHom hp2 L hline hstable))) = p :=
  S.card_residual_pointMap_image _ _ L hline (S.residual_descended_kernel_pointHom_ker hp2 L hline hstable)

/-- Cofixed直線から、同じℚ係数標的の非零有理p捩れ点を内部構成する。
同じ元P∉Lと既存の降下点関数の像であることを保持する。一般hnoは結論しない。 -/
theorem exists_rational_torsion_of_cofixed_kernel (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : (S.residualDescendedKernelModel L hline hL.isStable).toAffine.Point),
      P ∉ L ∧ p • R = 0 ∧ R ≠ 0 ∧
        baseChangePoint _ R = S.residualDescendedKernelPointMap hp2 L hline hL.isStable P.val :=
  S.exists_rational_torsion_of_cofixed_residual_pointMap _
    (S.residualDescendedKernelPointHom hp2 L hline hL.isStable) L hline
    (S.residual_descended_kernel_pointHom_ker hp2 L hline hL.isStable)
    (S.residual_descended_kernel_pointHom_equivariant hp2 L hline hL.isStable) hL

end DkMath.FLT.Frey.Source
