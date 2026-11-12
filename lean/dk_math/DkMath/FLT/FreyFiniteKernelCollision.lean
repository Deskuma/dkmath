/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelReductionSquare
import DkMath.Lib.NumberTheory.EllipticFiniteKernelCollision

#print "file: DkMath.FLT.FreyFiniteKernelCollision"

/-!
# 同じSourceの還元衝突点と、既存整数商像

q≠pで源の滑らかな点Pの還元が実核点Qの還元に一致するとき、
同じ付値環商像は滑らかでOへ還元する。整数化の単元条件は既存算術から供給し、
同じ既存整数点準同型の像の滑らかさも得る。良還元・悪還元・2の別を要求しない。
剰余核の外にある整点の輸送と、整数標的の剰余座標そのものの可換性は別の課題である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassModelReduction WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelCollision {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource・L・実核点Qへの還元衝突は、同じ商像の滑らかさとOへの還元を与える。
源でP=Qは要求しない。q≠pと両点の滑らかさを明示して保持する。 -/
theorem residual_pointHom_of_reduction_collision (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (Q : pointSubgroup S.rationalCurve p L)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hQ : HasSmoothReduction (S.valuationModel A) Q.val)
    (hr : modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P =
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl P) ∧
      modelReduce A (S.residualValuationKernelModel L hl hq hqp A hA) (S.residualKernelModel L hl)
        (S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl P) = 0 := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact oddKernelPointMap_of_reduction_collision S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hn (S.residual_pointSubgroup_odd hp2 L hl)
    P Q hP hQ hr

/-- 同じ衝突点の像を、既存の同じ整数標的へ輸送する。安定性は係数降下に必要な仮定。 -/
theorem residual_integer_pointHom_smooth_of_reduction_collision (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (Q : pointSubgroup S.rationalCurve p L)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hQ : HasSmoothReduction (S.valuationModel A) Q.val)
    (hr : modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P =
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
      (S.residualIntegerKernelPointHom hp2 L hl hs P) :=
  (S.residual_integer_pointHom_smooth_iff hp2 L hl hs hq hqp A hA P).mpr
    (S.residual_pointHom_of_reduction_collision hp2 L hl hq hqp A hA P Q hP hQ hr).1

end DkMath.FLT.Frey.Source
