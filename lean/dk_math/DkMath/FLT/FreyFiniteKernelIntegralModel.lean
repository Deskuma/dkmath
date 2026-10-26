/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelHom
import DkMath.Lib.NumberTheory.WeierstrassIntegralModelTransport

#print "file: DkMath.FLT.FreyFiniteKernelIntegralModel"

/-!
# 同じFrey有限核の整数係数標的と、その実点準同型・有理捩れ像

同じSource、残余直線L、既存のℚ係数標的Tを保持し、Tの共通分母dから実際のℤモデルを構成する。
そのℚ係数曲線への同じ幾何学的点の同型を使い、既存の準同型を移す。
核HとGalois同変性を保持し、Cofixedなら同じ整数モデル上の非零有理p捩れ点を得る。

dを割る素数で最小性や還元保持を仮定しない。元の曲線から商を取る過程での
局所還元保持・零成分輸送と、標的での有理捩れ排除は引き続き別の証明を必要とする。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open WeierstrassRationalIntegralModel DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelIntegralModel {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ既存ℚ係数標的の共通分母から構成した、実際のℤ係数曲線。 -/
noncomputable def residualIntegerKernelModel
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) : WeierstrassCurve ℤ :=
  integerModel (S.residualDescendedKernelModel L hline hstable)

/-- 同じ整数標的の判別式は、同じ既存有理標的の判別式のd¹²倍である。 -/
theorem residual_integer_kernel_model_discriminant
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    ((S.residualIntegerKernelModel L hline hstable).Δ : ℚ) =
      (commonDenominator (S.residualDescendedKernelModel L hline hstable) : ℚ) ^ 12 *
        (S.residualDescendedKernelModel L hline hstable).Δ :=
  integerModel_discriminant _

/-- 同じ整数標的の判別式は非零。ℤ上の単元性や全素数での良い還元を結論しない。 -/
theorem residual_integer_kernel_model_discriminant_ne_zero (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualIntegerKernelModel L hline hstable).Δ ≠ 0 := by
  let := S.residual_descended_kernel_model_isElliptic hp2 L hline hstable
  exact integerModel_discriminant_ne_zero _

/-- 同じ整数標的をℚへ戻した曲線は楕円曲線である。 -/
theorem residual_integer_kernel_model_isElliptic (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    ((S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ)).IsElliptic := by
  let := S.residual_descended_kernel_model_isElliptic hp2 L hline hstable
  exact integerModel_map_isElliptic _

/-- 同じ実点準同型を、同じ整数標的の幾何学的点へ移した加法準同型。 -/
noncomputable def residualIntegerKernelPointHom (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Points S.rationalCurve →+
      Points ((S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ)) :=
  (geometricPointEquiv (S.residualDescendedKernelModel L hline hstable)).symm.toAddMonoidHom.comp
    (S.residualDescendedKernelPointHom hp2 L hline hstable)

/-- 整数標的から同じ有理標的へ戻すと、既存の同じ点関数の像になる。 -/
theorem residual_integer_kernel_pointHom_transport (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) (P : Points S.rationalCurve) :
    geometricPointEquiv (S.residualDescendedKernelModel L hline hstable)
      (S.residualIntegerKernelPointHom hp2 L hline hstable P) =
        S.residualDescendedKernelPointMap hp2 L hline hstable P :=
  (geometricPointEquiv _).apply_symm_apply _

/-- 同じ整数標的への実点準同型の核は、同じ残余直線の実点核Hである。 -/
theorem residual_integer_kernel_pointHom_ker (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualIntegerKernelPointHom hp2 L hline hstable).ker = pointSubgroup S.rationalCurve p L := by
  ext P
  change (geometricPointEquiv (S.residualDescendedKernelModel L hline hstable)).symm
    (S.residualDescendedKernelPointHom hp2 L hline hstable P) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  exact S.residual_descended_kernel_pointMap_eq_zero_iff hp2 L hline hstable P

/-- 同じ整数標的への準同型は全射性も保持する。 -/
theorem residual_integer_kernel_pointHom_surjective (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Function.Surjective (S.residualIntegerKernelPointHom hp2 L hline hstable) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hs : Function.Surjective (S.residualDescendedKernelPointHom hp2 L hline hstable) :=
    descendedKernelPointHom_surjective S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)
      (pointSubgroup_stable S.rationalCurve p L hstable)
  exact (geometricPointEquiv _).symm.surjective.comp hs

/-- 同じ整数標的への準同型のp捩れ像の位数も、正確にpである。 -/
theorem card_residual_integer_kernel_torsion_image (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Nat.card (LinearMap.range (torsionPointMap S.rationalCurve
      ((S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ)) p
      (S.residualIntegerKernelPointHom hp2 L hline hstable))) = p :=
  S.card_residual_pointMap_image _ _ L hline (S.residual_integer_kernel_pointHom_ker hp2 L hline hstable)

/-- 同じ整数標的への準同型も、標準実点Galois作用と可換。 -/
theorem residual_integer_kernel_pointHom_equivariant (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualIntegerKernelPointHom hp2 L hline hstable (pointAction S.rationalCurve σ P) =
      pointAction ((S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ)) σ
        (S.residualIntegerKernelPointHom hp2 L hline hstable P) := by
  change (geometricPointEquiv _).symm
    (S.residualDescendedKernelPointHom hp2 L hline hstable (pointAction S.rationalCurve σ P)) = _
  rw [S.residual_descended_kernel_pointHom_equivariant]
  exact geometricPointEquiv_symm_equivariant _ σ _

/-- Cofixed直線から得た同じ非零有理p捩れ点を、同じ整数標的へ実際に移す。
元P∉L、捩れ性、非零性、同じ整数標的準同型との基底変換等式を保持する。 -/
theorem exists_rational_torsion_on_integer_kernel (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : ((S.residualIntegerKernelModel L hline hL.isStable).map (Int.castRingHom ℚ)).toAffine.Point),
      P ∉ L ∧ p • R = 0 ∧ R ≠ 0 ∧
        baseChangePoint _ R = S.residualIntegerKernelPointHom hp2 L hline hL.isStable P.val := by
  obtain ⟨P, R, hP, hpR, hR, he⟩ := S.exists_rational_torsion_of_cofixed_kernel hp2 L hline hL
  let T := S.residualDescendedKernelModel L hline hL.isStable
  let R' := (rationalPointEquiv T).symm R
  refine ⟨P, R', hP, ?_, ?_, ?_⟩
  · change p • (rationalPointEquiv T).symm R = 0
    rw [← map_nsmul, hpR, map_zero]
  · intro hz
    exact hR (((rationalPointEquiv T).apply_symm_apply R).symm.trans
      ((congrArg (rationalPointEquiv T) hz).trans (map_zero _)))
  · exact (geometricPointEquiv_symm_baseChange T R).symm.trans
      (congrArg (geometricPointEquiv T).symm he)

end DkMath.FLT.Frey.Source
