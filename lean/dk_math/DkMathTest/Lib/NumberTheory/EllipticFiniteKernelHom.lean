/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelHom
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelGlobal

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelHom"

/-!
同じy²=x³−x、非巡回の全3捩れ核E[3]（位数9）、非零2捩れ点R=(−1,0)を使用する。
既存点関数の加法性と商群同型、既存の非零主因子のAbel対応、
同じℚ係数標的への非零有理2捩れ像を検査する。
-/
namespace EllipticFiniteKernelHomTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open WeierstrassDivisorAbel WeierstrassFinitePlace
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest EllipticFiniteKernelNonsingularTest
open EllipticFiniteKernelPointDescentTest EllipticFiniteKernelGlobalTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 同じ全点関数が任意の二点について加法を保存する。 -/
theorem actual_additivity (P U : Points curve) :
    oddKernelPointMap curve fullThreeKernel fullThree_card.2 (P + U) =
      oddKernelPointMap curve fullThreeKernel fullThree_card.2 P +
        oddKernelPointMap curve fullThreeKernel fullThree_card.2 U :=
  oddKernelPointMap_add curve fullThreeKernel fullThree_card.2 P U

/-- 同じ非巡回9点核は、実際の加法準同型の核である。 -/
theorem actual_hom_kernel :
    (oddKernelPointHom curve fullThreeKernel fullThree_card.2).ker = fullThreeKernel :=
  oddKernelPointHom_ker curve fullThreeKernel fullThree_card.2

/-- 実際の商群から同じ標的へ得た同型は全単射である。 -/
theorem actual_quotient_bijective :
    Function.Bijective (oddKernelQuotientEquiv curve fullThreeKernel fullThree_card.2) :=
  (oddKernelQuotientEquiv curve fullThreeKernel fullThree_card.2).bijective

/-- 既存ℚ係数モデルの同じimage関数も、任意の二点の加法を保存する。 -/
theorem actual_descended_additivity (P U : Points curve) : image (P + U) = image P + image U :=
  (descendedKernelPointHom curve fullThreeKernel fullThree_card.2 fullThree_stable).map_add P U

/-- 既存の非零Weil主因子の点の総和は、同じ源の点群でOとなる。 -/
theorem actual_weil_abel :
    pointSum (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))) sourceDivisor = 0 := by
  apply pointSum_eq_zero_of_isPrincipal
  obtain ⟨f, hf, hd⟩ := actual_source_principal
  refine ⟨f, hf, ?_⟩
  change ∀ P : Points curve, sourceDivisor P =
    -WithZero.log (modelPointValuation (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P f)
  intro P
  exact (hd P).trans (congrArg (fun v => -WithZero.log (v f))
    (congrArg DFunLike.coe (geometric_modelPointValuation curve P)).symm)

/-- 非零点Rの点差因子は主因子ではない。主性の判定を無条件に緩めない境界検査。 -/
theorem actual_point_difference_not_principal :
    ¬ValuationDivisor.IsPrincipal
      (modelPointValuation (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))))
      (Finsupp.single R 1 - Finsupp.single 0 1) := by
  intro hp
  have he := pointSum_eq_zero_of_isPrincipal _ _ hp
  exact Point.some_ne_zero _
    ((pointSum_pointDivisor (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))) R).symm.trans he)

/-- 同じ源の任意の加法関係は、Oの係数を補正して実際の主因子になる。 -/
theorem actual_addition_principal (P U : Points curve) :
    ∃ n : ℤ, ValuationDivisor.IsPrincipal
      (modelPointValuation (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))))
      (Finsupp.single P 1 + Finsupp.single U 1 - Finsupp.single (P + U) 1 + Finsupp.single 0 n) :=
  addition_principal_correction (curve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P U

/-- 同じRの既存像は、加法性から実際の2捩れ点となる。 -/
theorem actual_image_two_torsion : 2 • image R = 0 := by
  change 2 • descendedKernelPointHom curve fullThreeKernel fullThree_card.2 fullThree_stable R = 0
  rw [← map_nsmul, actual_R_two_torsion, map_zero]

/-- 同じ既存ℚモデル上に、同じ像である非零有理2捩れ点を得る。 -/
theorem actual_nonzero_rational_two_torsion :
    ∃ T : target.toAffine.Point, baseChangePoint target T = image R ∧ T ≠ 0 ∧ 2 • T = 0 := by
  obtain ⟨T, he, hT⟩ := actual_coset_nonzero_rational_image (0 : fullThreeKernel)
  have ht : baseChangePoint target T = image R := by simpa only [ZeroMemClass.coe_zero, add_zero] using he
  refine ⟨T, ht, hT, ?_⟩
  apply baseChangePoint_injective target
  change baseChangePointHom target (2 • T) = baseChangePointHom target 0
  rw [map_nsmul, map_zero]
  change 2 • baseChangePoint target T = 0
  rw [ht]
  exact actual_image_two_torsion

end
end EllipticFiniteKernelHomTest
