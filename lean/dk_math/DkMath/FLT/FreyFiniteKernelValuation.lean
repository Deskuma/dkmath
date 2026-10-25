/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelPointDescent
import DkMath.Lib.NumberTheory.EllipticFiniteKernelValuation

#print "file: DkMath.FLT.FreyFiniteKernelValuation"

/-!
# 同じSourceの全点関数と局所付値の接続

同じ直線L・実点核H・二座標・標的モデル・引き戻しを保持する。
p≠2なら、Libの全点付値比較と軌道積の位数公式をそのまま利用できる。
核上の無限遠像を含み、局所倍率や場所の整合を外部仮定にしない。
標的の整数モデル、主因子の大域輸送、点の加法性とhnoはまだ結論しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceの同じ標的の全実点の正規化付値。 -/
noncomputable def residualKernelTargetValuation (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (T : (S.residualKernelModel L hline).toAffine.Point) :
    Valuation (S.residualKernelModel L hline).toAffine.FunctionField ℤᵐ⁰ := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ho : Odd (Nat.card (pointSubgroup S.rationalCurve p L)) := by
    rw [card_pointSubgroup S.rationalCurve p L hline]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  exact kernelTargetValuation S.rationalCurve _ ho T

/-- 同じSourceの全点関数と関数体引き戻しは、全ての局所付値を正確に保存する。 -/
theorem residual_kernel_model_pull_valuation_all (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) (g : (S.residualKernelModel L hline).toAffine.FunctionField) :
    pointValuation S.rationalCurve P (S.residualKernelModelPull L hline g) =
      S.residualKernelTargetValuation hp2 L hline (S.residualOddKernelPointMap hp2 L hline P) g := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ho : Odd (Nat.card (pointSubgroup S.rationalCurve p L)) := by
    rw [card_pointSubgroup S.rationalCurve p L hline]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  exact kernelModelPull_valuation_all S.rationalCurve _ ho P g

/-- 同じSourceの関数のH軌道積を、同じ標的関数体へ降ろした関数。 -/
noncomputable def residualKernelModelNorm
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (f : (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) :
    (S.residualKernelModel L hline).toAffine.FunctionField := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModelNorm S.rationalCurve (pointSubgroup S.rationalCurve p L) f

/-- 同じSourceの標的での軌道積位数公式。核上の点・Oも含み、局所倍率は1。 -/
theorem residual_kernel_model_norm_order_all (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) (f : (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField)
    (hf : f ≠ 0) :
    -log (S.residualKernelTargetValuation hp2 L hline (S.residualOddKernelPointMap hp2 L hline P)
      (S.residualKernelModelNorm L hline f)) =
      (let _ := S.finite_residualPointSubgroup L hline
       let _ := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
       ∑ Q : pointSubgroup S.rationalCurve p L, pointOrder S.rationalCurve (P + Q.val) f hf) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ho : Odd (Nat.card (pointSubgroup S.rationalCurve p L)) := by
    rw [card_pointSubgroup S.rationalCurve p L hline]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  exact kernelModelNorm_order_all S.rationalCurve _ ho P f hf

end DkMath.FLT.Frey.Source
