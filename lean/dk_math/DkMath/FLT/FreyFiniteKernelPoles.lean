/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernel
import DkMath.Lib.NumberTheory.EllipticFiniteKernelPoles

#print "file: DkMath.FLT.FreyFiniteKernelPoles"

/-!
# NOTE-032-005C₂b: 同じFrey正規化座標和の極

同じSource、同じ直線Lから構成済みの二つの関数について、
非定数性と極の支持・局所位数を一般核から供給する。
極の計算にはガロア安定性やCofixed性は不要。これらは別に係数降下で使う。
商曲線方程式や点群写像はまだ構成していない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instSourceCurveEllipticFiniteKernelPoles : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceの二つの構成済み関数は、代数閉包のどの定数とも異なる。 -/
theorem residual_kernel_coordinates_nonconstant
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (c : AlgebraicClosure ℚ) :
    S.residualKernelX L hline ≠ algebraMap (AlgebraicClosure ℚ)
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c ∧
      S.residualKernelY L hline ≠ algebraMap (AlgebraicClosure ℚ)
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact ⟨veluX_ne_const S.rationalCurve _ c, veluY_ne_const S.rationalCurve _ c⟩

/-- 同じ実点核の全ての点で、二関数の付値はexp(2),exp(3)である。
Freyの2進付値ではなく、曲線の関数体の点付値であることを区別する。 -/
theorem residual_kernel_coordinate_valuations_of_mem
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) (hP : P ∈ pointSubgroup S.rationalCurve p L) :
    pointValuation S.rationalCurve P (S.residualKernelX L hline) = exp (2 : ℤ) ∧
      pointValuation S.rationalCurve P (S.residualKernelY L hline) = exp (3 : ℤ) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact ⟨veluX_valuation_of_mem S.rationalCurve _ P hP,
    veluY_valuation_of_mem S.rationalCurve _ P hP⟩

/-- 同じSourceの二関数の極の支持は、正確に同じ直線の実点群内の像である。 -/
theorem residual_kernel_coordinate_pole_support
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Points S.rationalCurve) :
    (1 < pointValuation S.rationalCurve P (S.residualKernelX L hline) ↔
      P ∈ pointSubgroup S.rationalCurve p L) ∧
    (1 < pointValuation S.rationalCurve P (S.residualKernelY L hline) ↔
      P ∈ pointSubgroup S.rationalCurve p L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact velu_pole_support S.rationalCurve _ P

end DkMath.FLT.Frey.Source
