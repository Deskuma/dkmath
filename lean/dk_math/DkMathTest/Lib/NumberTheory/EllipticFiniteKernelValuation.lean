/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelValuation
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPointDescent

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelValuation"

/-!
同じ曲線y²=x³−x、位数9の全3捩れ核、R=(−1,0)を使う。
有限像点・核上の無限遠像・軌道積の全点位数を確認する。
付値を二乗した例も作り、場所の中心だけでは正規化は決まらないことを検査する。
-/
namespace EllipticFiniteKernelValuationTest
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest EllipticFiniteKernelNonsingularTest
open EllipticFiniteKernelPointDescentTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq fullThreeKernel := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 同じ位数9の核の全点関数が、全ての関数について付値を正確に保存する。 -/
theorem actual_allpoint_valuation (P : Points curve)
    (g : (kernelModel curve fullThreeKernel).toAffine.FunctionField) :
    pointValuation curve P (kernelModelPull curve fullThreeKernel g) =
      kernelTargetValuation curve fullThreeKernel fullThree_card.2
        (oddKernelPointMap curve fullThreeKernel fullThree_card.2 P) g :=
  kernelModelPull_valuation_all curve fullThreeKernel fullThree_card.2 P g

/-- 同じ核の任意の点では、源の付値が標的の無限遠付値に一致する。 -/
theorem actual_kernel_infinity (Q : fullThreeKernel)
    (g : (kernelModel curve fullThreeKernel).toAffine.FunctionField) :
    pointValuation curve Q.val (kernelModelPull curve fullThreeKernel g) =
      EllipticInfinityValuation.valuationInfty (kernelModel curve fullThreeKernel).toAffine g :=
  kernelModelPull_valuation_of_mem curve fullThreeKernel Q.val Q.property g

/-- 実際の有限点Rでも同じ比較が成立する。 -/
theorem actual_finite_valuation (g : (kernelModel curve fullThreeKernel).toAffine.FunctionField) :
    pointValuation curve R (kernelModelPull curve fullThreeKernel g) =
      kernelImageValuation curve fullThreeKernel fullThree_card.2 R actual_R_outside g :=
  kernelModelPull_valuation_eq curve fullThreeKernel fullThree_card.2 R actual_R_outside g

/-- CRTにより、Rの同じ9点軌道で一点だけを一次で消す関数を内部構成できる。 -/
theorem actual_orbit_parameter :
    ∃ f : (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField, f ≠ 0 ∧
      ∀ Q : fullThreeKernel, pointValuation curve (R + Q.val) f =
        if Q = 0 then exp (-1 : ℤ) else 1 := by
  obtain ⟨f, hf, hv⟩ := exists_orbit_parameter curve fullThreeKernel R actual_R_outside
  refine ⟨f, hf, fun Q => ?_⟩
  by_cases hQ : Q = 0
  · simpa only [ite_eq_left hQ] using hv Q
  · simpa only [ite_eq_right hQ] using hv Q

/-- 標的の同じ有限像点で、位数1の一様化元を得る。局所倍率1の外部仮定は不要。 -/
theorem actual_target_uniformizer :
    ∃ g : (kernelModel curve fullThreeKernel).toAffine.FunctionField, g ≠ 0 ∧
      kernelImageValuation curve fullThreeKernel fullThree_card.2 R actual_R_outside g = exp (-1 : ℤ) := by
  obtain ⟨g, hg, he⟩ := exists_kernel_pull_uniformizer curve fullThreeKernel R actual_R_outside
  exact ⟨g, hg, (actual_finite_valuation g).symm.trans he⟩

/-- 同じ全点関数の標的での軌道積位数公式は、Oと核上の点を含む。 -/
theorem actual_norm_allpoint (P : Points curve)
    (f : (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) (hf : f ≠ 0) :
    -log (kernelTargetValuation curve fullThreeKernel fullThree_card.2
      (oddKernelPointMap curve fullThreeKernel fullThree_card.2 P) (kernelModelNorm curve fullThreeKernel f)) =
      ∑ Q : fullThreeKernel, pointOrder curve (P + Q.val) f hf :=
  kernelModelNorm_order_all curve fullThreeKernel fullThree_card.2 P f hf

/-- 前回は源で計算した位数−18を、今回は同じ標的のOで証明する。 -/
theorem actual_target_norm_pole_order :
    -log (EllipticInfinityValuation.valuationInfty (kernelModel curve fullThreeKernel).toAffine
      (kernelModelNorm curve fullThreeKernel (veluX curve fullThreeKernel))) = -18 := by
  have hv := actual_kernel_infinity (0 : fullThreeKernel)
    (kernelModelNorm curve fullThreeKernel (veluX curve fullThreeKernel))
  rw [kernelModelPull_norm] at hv
  have hp := actual_norm_pole_order
  rw [pointOrder_eq_neg_log] at hp
  exact (congrArg (fun z => -log z) hv).symm.trans hp

/-- 正規化を変えた実際の付値。同じ点Rの付値を二乗する。 -/
def doubledValuation : Valuation (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ℤᵐ⁰ :=
  Valuation.map (powMonoidWithZeroHom (by decide : 2 ≠ 0))
    (fun _ _ h => pow_le_pow_left₀ zero_le h 2) (pointValuation curve R)

/-- 二乗付値の整数位数は2倍になる。付値であることだけから倍率1を導かない。 -/
theorem actual_doubled_order (f : (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) :
    -log (doubledValuation f) = 2 * (-log (pointValuation curve R f)) := by
  change -log (pointValuation curve R f ^ 2) = _
  rw [log_pow]
  simp only [nsmul_eq_mul]
  ring

/-- 同じ局所パラメータで、正規化の違いexp(−1)とexp(−2)を実際に分離する。 -/
theorem actual_normalization_guard :
    ∃ f : (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField,
      pointValuation curve R f = exp (-1 : ℤ) ∧ doubledValuation f = exp (-2 : ℤ) := by
  obtain ⟨f, _, hv⟩ := actual_orbit_parameter
  have hf : pointValuation curve R f = exp (-1 : ℤ) := by
    simpa using hv 0
  refine ⟨f, hf, ?_⟩
  change pointValuation curve R f ^ 2 = _
  rw [hf, ← exp_nsmul]
  norm_num

end
end EllipticFiniteKernelValuationTest
