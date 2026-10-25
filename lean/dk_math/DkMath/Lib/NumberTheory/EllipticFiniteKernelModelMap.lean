/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelModel
import DkMath.Lib.NumberTheory.WeierstrassCoordinateEvaluation

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelModelMap"

/-!
# 標的モデルの関数体を、同じ平行移動固定体として実現する

[DkMath.Lib] 明るい側: 同じ座標に対するモデルの一意性、実際の座標環単射、
分数体の引き戻し、その像が同じF_Hに等しいこと、関数体次数|H|。
暗い側: 全点で正則な群準同型、標的のΔ≠0、点核の一致はまだここに含まれない。
特異三次曲線でも一般点と関数体は存在するため、この区別を型に残す。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation EllipticFunctionField
open WeierstrassCoordinateEvaluation
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelModelMap :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じ二関数の方程式と元のa₁,a₃を指定すると、構成したモデルは一意。 -/
theorem kernelModel_unique (H : AddSubgroup (Points E)) [Fintype H]
    (W : WeierstrassCurve (AlgebraicClosure K))
    (h₁ : W.a₁ = (E⁄(AlgebraicClosure K)).a₁) (h₃ : W.a₃ = (E⁄(AlgebraicClosure K)).a₃)
    (he : (W.toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation
      (veluX E H) (veluY E H)) : W = kernelModel E H :=
  eq_of_same_equation W (veluX E H) (veluY E H) (kernelModel E H)
    (veluX_transcendental E H) (h₁.trans (kernelModel_a₁ E H).symm)
    (h₃.trans (kernelModel_a₃ E H).symm) he (kernelModel_equation E H)

/-- [DkMath.Lib] 標的モデルの実際の座標環から、元の楕円関数体への代入。 -/
noncomputable def kernelModelCoordinateHom (H : AddSubgroup (Points E)) [Fintype H] :
    (kernelModel E H).toAffine.CoordinateRing →ₐ[AlgebraicClosure K]
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  coordinateEval (kernelModel E H) (veluX E H) (veluY E H) (kernelModel_equation E H)

/-- [DkMath.Lib] モデルの座標環代入の核は零。一般点の非特異性だけを理由にはしない。 -/
theorem kernelModelCoordinateHom_injective (H : AddSubgroup (Points E)) [Fintype H] :
    Function.Injective (kernelModelCoordinateHom E H) :=
  coordinateEval_injective (kernelModel E H) _ _ (kernelModel_equation E H)
    (veluX_transcendental E H) (veluY_not_mem_simpleX E H)

/-- [DkMath.Lib] 同じモデルの分数体からの実際の引き戻し。定義に標的楕円性を要求しない。 -/
noncomputable def kernelModelPull (H : AddSubgroup (Points E)) [Fintype H] :
    (kernelModel E H).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  functionPull (kernelModel E H) _ _ (kernelModel_equation E H)
    (veluX_transcendental E H) (veluY_not_mem_simpleX E H)

/-- [DkMath.Lib] 関数体準同型なので、モデルからの引き戻しも単射である。 -/
theorem kernelModelPull_injective (H : AddSubgroup (Points E)) [Fintype H] :
    Function.Injective (kernelModelPull E H) := (kernelModelPull E H).injective

/-- [DkMath.Lib] 引き戻しの像は同じ二関数の生成体、従って同じHの平行移動固定体である。 -/
theorem kernelModelPull_fieldRange (H : AddSubgroup (Points E)) [Fintype H] :
    (kernelModelPull E H).fieldRange = kernelFixedField E H := by
  rw [kernelModelPull, functionPull_fieldRange]
  exact veluCoordinateField_eq_fixedField E H

/-- [DkMath.Lib] 同じモデルからの実際の関数体引き戻しの次数は|H|。
全点写像やisogenyの次数とは、定理の型を区別する。 -/
theorem finrank_kernelModelPull (H : AddSubgroup (Points E)) [Fintype H] :
    Module.finrank (kernelModelPull E H).fieldRange
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField = Nat.card H := by
  rw [kernelModelPull_fieldRange]
  exact finrank_kernelFixedField E H

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
