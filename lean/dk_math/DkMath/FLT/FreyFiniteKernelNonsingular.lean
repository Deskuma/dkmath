/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelSpecialization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular

#print "file: DkMath.FLT.FreyFiniteKernelNonsingular"

/-!
# 同じ奇素数核の標的楕円性を、追加providerなしで供給する

p≠2なら同じ直線Lの実点核の位数pは奇数。
Libの有限ファイバー計数と三根判定から、同じresidualKernelModelのΔ≠0を得る。
標的IsEllipticを外部入力にしていた全点関数と零ファイバーを、この定理で無条件化する。
加法性・isogeny・整数係数・局所還元や零成分輸送は、この入口の結論には含まれない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceの奇素数核の標的判別式は非零。三値分離の追加入力は不要。 -/
theorem residual_kernel_model_discriminant_ne_zero (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (S.residualKernelModel L hline).Δ ≠ 0 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  apply kernelModel_discriminant_ne_zero_of_odd_card S.rationalCurve
  rw [card_pointSubgroup S.rationalCurve p L hline]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2

/-- 同じ標的IsEllipticを実際に供給する。奇素数・同じ一次元直線の入力だけを保持する。 -/
theorem residual_kernel_model_isElliptic (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (S.residualKernelModel L hline).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (S.residual_kernel_model_discriminant_ne_zero hp2 L hline)⟩

/-- 同じ核の外の全実点で、特殊化した標的点の非特異性を内部供給する。 -/
theorem residual_kernel_at_nonsingular (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) (hP : P ∉ pointSubgroup S.rationalCurve p L) :
    (S.residualKernelModel L hline).toAffine.Nonsingular
      (S.residualKernelXAt L hline P hP) (S.residualKernelYAt L hline P hP) := by
  let := S.residual_kernel_model_isElliptic hp2 L hline
  exact equation_iff_nonsingular.mp (S.residual_kernel_at_equation L hline P hP)

/-- 同じ全点関数を、標的楕円性の追加入力なしで公開する。群準同型ではまだない。 -/
noncomputable def residualOddKernelPointMap (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Points S.rationalCurve → (S.residualKernelModel L hline).toAffine.Point := by
  let := S.residual_kernel_model_isElliptic hp2 L hline
  exact S.residualKernelPointMap L hline

/-- 同じ全点関数の零ファイバーHは、標的IsEllipticの外部providerなしで確定する。 -/
theorem residual_odd_kernel_pointMap_eq_zero_iff (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) :
    S.residualOddKernelPointMap hp2 L hline P = 0 ↔ P ∈ pointSubgroup S.rationalCurve p L := by
  let := S.residual_kernel_model_isElliptic hp2 L hline
  exact S.residual_kernel_pointMap_eq_zero_iff L hline P

/-- 同じ安定直線のℚ係数モデルも実際に楕円曲線となる。整数係数への降下とは区別する。 -/
theorem exists_rational_elliptic_residual_kernel_model (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    ∃ W : WeierstrassCurve ℚ,
      W.map (algebraMap ℚ (AlgebraicClosure ℚ)) = S.residualKernelModel L hline ∧
      W.IsElliptic ∧ W.a₁ = S.rationalCurve.a₁ ∧ W.a₃ = S.rationalCurve.a₃ := by
  obtain ⟨W, hW, h₁, h₃⟩ := S.exists_rational_residual_kernel_model L hline hstable
  refine ⟨W, hW, ?_, h₁, h₃⟩
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  intro hz
  have h := congrArg WeierstrassCurve.Δ hW
  rw [WeierstrassCurve.map_Δ, hz, map_zero] at h
  exact S.residual_kernel_model_discriminant_ne_zero hp2 L hline h.symm

end DkMath.FLT.Frey.Source
