/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelPoles
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDegree

#print "file: DkMath.FLT.FreyFiniteKernelDegree"

/-!
# NOTE-032-005C₂c₁: 同じSourceの有限次数と条件付き生成

同じ構成済み二関数の単純部分体に対する有限性を内部供給する。
Y_Hのモニック関係も同じ関数体と同じX_H上に構成する。
正確な次数2p,3pを与えれば二関数は同じ核の固定体を生成するが、
その二つの次数は今回未証明の入力である。標的曲線やisogenyの存在を結論しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IntermediateField Polynomial
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instSourceCurveEllipticFiniteKernelDegree : S.rationalCurve.IsElliptic :=
  S.rationalCurve_isElliptic

/-- 同じSourceの構成済みX_H,Y_Hそれぞれに対する関数体拡大は有限である。 -/
theorem residual_kernel_function_degrees_finite
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    FiniteDimensional (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ∧
      FiniteDimensional (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact finiteDimensional_over_velu S.rationalCurve _

/-- 同じ二関数の生成体が、同じ直線の実点核の固定体に含まれることを確認する。 -/
theorem residual_kernel_coordinateField_le_fixedField
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} ≤
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact veluCoordinateField_le_fixedField S.rationalCurve _

/-- 同じSourceのY_Hは、同じX_Hの単純部分体上で正次数モニック関係を持つ。
次数2、Weierstrass形、非特異性を主張するものではない。 -/
theorem exists_residual_kernel_monic_relation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    ∃ q : ((AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯)[X],
      q.Monic ∧ 0 < q.natDegree ∧ aeval (S.residualKernelY L hline) q = 0 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact exists_velu_monic_relation S.rationalCurve _

/-- 同じSourceの単純部分体の正確な次数2p,3pを供給すれば、同じ固定体を生成する。
二つの次数は未供給の仮定として保持し、極位数の総和を代入して閉じたとはしない。 -/
theorem residual_kernel_coordinateField_eq_fixedField_of_degrees
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hX : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 2 * p)
    (hY : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 3 * p) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  apply veluCoordinateField_eq_fixedField_of_degrees S.rationalCurve (pointSubgroup S.rationalCurve p L)
  · rw [card_pointSubgroup S.rationalCurve p L hline]
    exact hX
  · rw [card_pointSubgroup S.rationalCurve p L hline]
    exact hY

end DkMath.FLT.Frey.Source
