/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelDegree
import DkMath.Lib.NumberTheory.EllipticFiniteKernelGeneration

#print "file: DkMath.FLT.FreyFiniteKernelGeneration"

/-!
# 同じSourceの次数と固定体生成

構成済みの同じ残余核と正規化二関数を使う。
前回入力に残った次数2p,3pは極空間から内部供給できるようになった。
商の標的方程式・点準同型・零成分の輸送は、この関数体生成とは別の構成である。
-/
namespace DkMath.FLT.Frey.Source
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instSourceCurveEllipticFiniteKernelGeneration : S.rationalCurve.IsElliptic :=
  S.rationalCurve_isElliptic

/-- 同じ実点核の固定体の、二つの単純部分体に対する相対次数は2,3。 -/
theorem residual_kernel_relative_degrees
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    ((AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯).relfinrank
        (kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L)) = 2 ∧
    ((AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯).relfinrank
        (kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L)) = 3 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact velu_relative_degrees S.rationalCurve _

/-- 同じSourceの構成済み二関数について、正確な次数2p,3pを内部供給する。 -/
theorem residual_kernel_function_degrees
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 2 * p ∧
    Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 3 * p := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ht := velu_ambient_degrees S.rationalCurve (pointSubgroup S.rationalCurve p L)
  rw [card_pointSubgroup S.rationalCurve p L hline] at ht
  exact ht

/-- 同じ二関数が同じ核の固定体を生成する。次数や生成の外部providerは不要となる。 -/
theorem residual_kernel_coordinateField_eq_fixedField
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact veluCoordinateField_eq_fixedField S.rationalCurve _

/-- 同じY_Hの最小多項式の次数は、同じX_H上で正確に2。 -/
theorem natDegree_residual_kernel_minpoly
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (minpoly (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
      (S.residualKernelY L hline)).natDegree = 2 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact natDegree_minpoly_veluY S.rationalCurve _

/-- 同じSourceの実際のモニック二次関係。Weierstrass形や標的楕円性は含めない。 -/
theorem exists_residual_kernel_quadratic_relation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    ∃ q : ((AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯)[X],
      q.Monic ∧ q.natDegree = 2 ∧ aeval (S.residualKernelY L hline) q = 0 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact exists_velu_quadratic_relation S.rationalCurve _

end DkMath.FLT.Frey.Source
