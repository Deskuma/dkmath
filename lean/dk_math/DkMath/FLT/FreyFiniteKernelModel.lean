/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGeneration
import DkMath.Lib.NumberTheory.EllipticFiniteKernelModelDescent

#print "file: DkMath.FLT.FreyFiniteKernelModel"

/-!
# 同じSourceから三次モデルとその関数体引き戻しへ

明: 同じ残余核・同じ二関数を保つモデル、方程式、一般点、実際の関数体単射と次数p。
同じ直線が安定なら、モデルをℚ係数へ降下できる。
暗: モデルのΔ≠0、全点でのisogeny、標的零成分への輸送はまだ証明していない。
-/
namespace DkMath.FLT.Frey.Source
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instSourceCurveEllipticFiniteKernelModel : S.rationalCurve.IsElliptic :=
  S.rationalCurve_isElliptic

/-- 同じ残余核の代数閉包係数モデル。IsEllipticをデータに含めない。 -/
noncomputable def residualKernelModel (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) : WeierstrassCurve (AlgebraicClosure ℚ) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 同じ構成済み二関数が、同じモデルの実際の方程式を満たす。 -/
theorem residual_kernel_model_equation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    ((S.residualKernelModel L hline).toAffine⁄
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
        (S.residualKernelX L hline) (S.residualKernelY L hline) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModel_equation S.rationalCurve _

/-- 同じ二関数の関数体値点は非特異。モデル全体の非特異性とは区別する。 -/
theorem residual_kernel_model_generic_nonsingular
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    ((S.residualKernelModel L hline).toAffine⁄
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Nonsingular
        (S.residualKernelX L hline) (S.residualKernelY L hline) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModel_generic_nonsingular S.rationalCurve _

/-- 同じモデルの関数体から、同じSourceの関数体への実際の引き戻し。 -/
noncomputable def residualKernelModelPull (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) :
    (S.residualKernelModel L hline).toAffine.FunctionField →ₐ[AlgebraicClosure ℚ]
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModelPull S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 同じSourceの引き戻し像は、同じ実点核の平行移動固定体。 -/
theorem residual_kernel_model_fieldRange
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (S.residualKernelModelPull L hline).fieldRange =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModelPull_fieldRange S.rationalCurve _

/-- 同じモデルの関数体引き戻しの次数はp。点isogenyの次数とはまだ結論しない。 -/
theorem finrank_residual_kernel_model_pull
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Module.finrank (S.residualKernelModelPull L hline).fieldRange
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = p := by
  rw [S.residual_kernel_model_fieldRange]
  let := S.finite_residualPointSubgroup L hline
  rw [finrank_kernelFixedField, card_pointSubgroup S.rationalCurve p L hline]

/-- 同じ直線の安定性から、同じモデルのℚ係数表示を構成する。楕円性は含めない。 -/
theorem exists_rational_residual_kernel_model
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    ∃ W : WeierstrassCurve ℚ, W.map (algebraMap ℚ (AlgebraicClosure ℚ)) = S.residualKernelModel L hline ∧
      W.a₁ = S.rationalCurve.a₁ ∧ W.a₃ = S.rationalCurve.a₃ := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact exists_descended_kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)
    (pointSubgroup_stable S.rationalCurve p L hstable)

end DkMath.FLT.Frey.Source
