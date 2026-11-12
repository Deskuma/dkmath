/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPointDescent
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNorm
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNonsingular

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPointDescent"

/-!
位数9の全3捩れ核を保ち、同じ商座標をℚ係数モデルの実点として調べる。
R=(−1,0)は核外の有理2捩れ点。R+Q (Q∈E[3])という剰余類全体は
Galois作用で安定なので、個々のQの有理性なしに像が非零有理点へ降りる。
像の捩れ性をテストの仮定や結論へ混入させない。
-/
namespace EllipticFiniteKernelPointDescentTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFunctionField
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest EllipticFiniteKernelNonsingularTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 同じ位数9の安定核から降下した実際のℚ係数楕円曲線。 -/
abbrev target := descendedKernelModel curve fullThreeKernel fullThree_stable

/-- 同じ二つの特殊化値とH上のOから構成した全点関数。 -/
def image : Points curve → Points target :=
  descendedKernelPointMap curve fullThreeKernel fullThree_card.2 fullThree_stable

/-- 同じ全点関数について、有限点もOも含めて標準Galois作用と可換。 -/
theorem actual_equivariance (σ : Field.absoluteGaloisGroup ℚ) (P : Points curve) :
    image (pointAction curve σ P) = pointAction target σ (image P) :=
  descendedKernelPointMap_equivariant curve fullThreeKernel fullThree_card.2 fullThree_stable σ P

/-- 同じ9点核に対する零ファイバー。群準同型の核という表記はまだ使わない。 -/
theorem actual_zero_fiber (P : Points curve) : image P = 0 ↔ P ∈ fullThreeKernel :=
  descendedKernelPointMap_eq_zero_iff curve fullThreeKernel fullThree_card.2 fullThree_stable P

/-- モデルの等式による移送で、前回の同じ全点関数に一致する。 -/
theorem actual_same_map (P : Points curve) :
    pointModelEquiv (descendedKernelModel_map curve fullThreeKernel fullThree_stable) (image P) =
      oddKernelPointMap curve fullThreeKernel fullThree_card.2 P :=
  descendedKernelPointMap_transport curve fullThreeKernel fullThree_card.2 fullThree_stable P

/-- 同じ非巡回9点核の全点関数は反転も保存する。 -/
theorem actual_inversion (P : Points curve) : image (-P) = -image P :=
  descendedKernelPointMap_neg curve fullThreeKernel fullThree_card.2 fullThree_stable P

/-- Rの反転固定性は同じ実点群内で計算できる。 -/
theorem actual_R_fixed : -R = R := by
  change -Point.some _ _ _ = Point.some _ _ _
  rw [Point.neg_some]
  norm_num [curve, baseChangePoint, rationalR, R]

/-- 2捩れの非零点Rは奇数位数9の核に入らない。 -/
theorem actual_R_outside : R ∉ fullThreeKernel := by
  intro h
  exact Point.some_ne_zero _
    (eq_zero_of_mem_odd_kernel_fixed curve fullThreeKernel fullThree_card.2 R h actual_R_fixed)

/-- R+E[3]全体がGalois安定。一点ごとの有理性を仮定しない実際の剰余類の例。 -/
theorem actual_fixed_coset (Q : fullThreeKernel) (σ : Field.absoluteGaloisGroup ℚ) :
    ∃ D : fullThreeKernel, pointAction curve σ (R + Q.val) = (R + Q.val) + D.val := by
  let D : fullThreeKernel := ⟨pointAction curve σ Q.val - Q.val,
    fullThreeKernel.sub_mem (fullThree_stable σ Q.val Q.property) Q.property⟩
  refine ⟨D, ?_⟩
  have hR : pointAction curve σ R = R := pointAction_baseChange curve σ rationalR
  have ha := (pointAction curve σ).map_add R Q.val
  calc
    pointAction curve σ (R + Q.val) = R + pointAction curve σ Q.val := by rw [ha, hR]
    _ = (R + Q.val) + D.val := by change _ = (R + Q.val) + (_ - Q.val); abel

/-- 任意の幾何学的Q∈E[3]について、R+Qの像は非零ℚ有理点へ実際に降下する。
入力点R+Q自体が有理であるとの仮定を置かない。 -/
theorem actual_coset_nonzero_rational_image (Q : fullThreeKernel) :
    ∃ T : target.toAffine.Point, baseChangePoint target T = image (R + Q.val) ∧ T ≠ 0 := by
  obtain ⟨T, he, hz⟩ := exists_rational_image_of_fixed_coset curve fullThreeKernel
    fullThree_card.2 fullThree_stable (R + Q.val) (actual_fixed_coset Q)
  refine ⟨T, he, fun h => ?_⟩
  have hm := hz.mp h
  exact actual_R_outside ((fullThreeKernel.add_mem_cancel_right Q.property).mp hm)

/-- Rの同じ剰余類では全点関数は一定である。これは任意の二点の加法性ではない。 -/
theorem actual_coset_image (Q : fullThreeKernel) : image (R + Q.val) = image R :=
  descendedKernelPointMap_translation curve fullThreeKernel fullThree_card.2 fullThree_stable R Q

/-- 非定数関数xの軌道積を同じ標的関数体へ一意に降ろせる。
像の関数は非零で、引き戻しは同じ9因子の積。 -/
theorem actual_norm_of_x :
    ∃! g : (kernelModel curve fullThreeKernel).toAffine.FunctionField,
      kernelModelPull curve fullThreeKernel g =
        kernelNorm curve fullThreeKernel (genericX curve (AlgebraicClosure ℚ)) :=
  existsUnique_kernelModelNorm curve fullThreeKernel _

/-- 同じ標的へ降ろしたxの軌道積は非零。 -/
theorem actual_norm_of_x_ne_zero :
    kernelModelNorm curve fullThreeKernel (genericX curve (AlgebraicClosure ℚ)) ≠ 0 :=
  kernelModelNorm_ne_zero curve fullThreeKernel _
    (by simpa only [map_zero] using genericX_ne_algebraMap curve (AlgebraicClosure ℚ) 0)

/-- X_Hは固定関数なので、9点の軌道積はX_Hの9乗となる。 -/
theorem actual_norm_fixed_coordinate :
    kernelNorm curve fullThreeKernel (veluX curve fullThreeKernel) =
      veluX curve fullThreeKernel ^ 9 := by
  have h := kernelNorm_of_mem curve fullThreeKernel _ (velu_coordinates_mem curve fullThreeKernel).1
  simpa only [Fintype.card_eq_nat_card, fullThree_card.1] using h

/-- 源のOでの位数は9個の−2の和で−18。標的での位数との混同を防ぐ。 -/
theorem actual_norm_pole_order :
    pointOrder curve 0 (kernelNorm curve fullThreeKernel (veluX curve fullThreeKernel))
      (kernelNorm_ne_zero curve fullThreeKernel _ (veluX_ne_zero curve fullThreeKernel)) = -18 := by
  have hp := pointOrder_kernelNorm curve fullThreeKernel 0
    (veluX curve fullThreeKernel) (veluX_ne_zero curve fullThreeKernel)
  have hQ (Q : fullThreeKernel) :
      pointOrder curve (0 + Q.val) (veluX curve fullThreeKernel)
        (veluX_ne_zero curve fullThreeKernel) = -2 := by
    simpa only [zero_add] using (velu_orders_of_mem curve fullThreeKernel Q.val Q.property).1
  simp only [hQ, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    fullThree_card.1] at hp
  norm_num at hp
  exact hp

end
end EllipticFiniteKernelPointDescentTest
