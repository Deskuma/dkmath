/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff.lean.
Upstream blob: f70f027f91903199d7019d7256810f37e761687a
Modified for DkMath: include the identity as the unit ideal and provide an integral-ideal criterion.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces

#print "file: DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal"

/-!
# 点の総和と、点イデアルの積の主性

MathlibのPoint.toClassは、点群から同じ曲線の座標環の類群への単射な加法準同型である。
整数係数の点の和が零になることと、対応する分数イデアルの積が主であることを同値にする。
無限遠点Oには単位イデアルを割り当て、有限点の積からOを除く操作を正確に表す。
Oに素イデアルや局所付値を割り当てたという意味ではない。
円分整数環の類群とは異なる対象であり、Kummerの類群条件は使わない。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors
namespace DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

open Classical in
/-- 整数係数の点の総和と主分数イデアルの対応。負の指数は逆分数イデアルを表す。 -/
theorem isPrincipal_prod_XYIdeal_zpow_iff {ι : Type*} (s : Finset ι)
    (x y : ι → F) (h : ∀ i, W.Nonsingular (x i) (y i)) (m : ι → ℤ) :
    ((∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i :
      (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
      Submodule W.CoordinateRing W.FunctionField).IsPrincipal ↔
      ∑ i ∈ s, m i • Point.some (x i) (y i) (h i) = 0 := by
  rw [← ClassGroup.mk_eq_one_iff, ← Point.toClass_eq_zero, map_sum]
  have key : Additive.toMul (∑ i ∈ s, Point.toClass (m i • Point.some (x i) (y i) (h i))) =
      ClassGroup.mk W.FunctionField (∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i) := by
    rw [map_prod, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zsmul, toMul_zsmul, map_zpow, Point.toClass_some]
    rfl
  rw [← key]
  exact Additive.toMul.eq_symm_apply.symm

open Classical in
/-- 有限点には座標差イデアル、Oには単位イデアルを割り当てる。
積の中でOを省くための規約であり、Oがアフィン素点であるという主張ではない。 -/
noncomputable def pointIdeal (P : W.Point) : Ideal W.CoordinateRing :=
  match P with
  | .zero => ⊤
  | .some x y _ => CoordinateRing.XYIdeal W x (C y)

open Classical in
/-- 同じ点イデアルを、可逆な分数イデアルとして保持する。 -/
noncomputable def pointIdealUnit (P : W.Point) : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  match P with
  | .zero => 1
  | .some _ _ h => CoordinateRing.XYIdeal' h

open Classical in
/-- Oの寄与は積の単位元である。 -/
@[simp] theorem pointIdeal_zero : pointIdeal (0 : W.Point) = ⊤ := rfl

open Classical in
/-- 非零点のイデアルはNOTE-021で構成した同じ場所の素イデアルである。 -/
theorem pointIdeal_of_ne_zero {P : W.Point} (hP : P ≠ 0) :
    pointIdeal P = CoordinateRing.XYIdeal W P.xc (C P.yc) := by
  rw [Point.eq_some_xc_yc hP]
  rfl

open Classical in
/-- 整イデアルと可逆分数イデアルは、同じ座標差の部分加群を表す。 -/
theorem coe_pointIdealUnit (P : W.Point) :
    (pointIdealUnit P : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      (pointIdeal P : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  cases P with
  | zero =>
    change (1 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      ((⊤ : Ideal W.CoordinateRing) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
    rw [← Ideal.one_eq_top]
    exact (FractionalIdeal.coeIdealHom W.CoordinateRing⁰ W.FunctionField).map_one.symm
  | some x y h => exact CoordinateRing.XYIdeal'_eq h

open Classical in
/-- 各点の類は、選んだ同じ可逆分数イデアルの類である。 -/
theorem toClass_eq_mk (P : W.Point) :
    Point.toClass P = ClassGroup.mk W.FunctionField (pointIdealUnit P) := by
  cases P with
  | zero => exact (ClassGroup.mk W.FunctionField).map_one.symm
  | some _ _ h => exact Point.toClass_some h

open Classical in
/-- 点イデアルは零でない。Oの単位イデアルと、有限点の非零素イデアルを区別して示す。 -/
theorem pointIdeal_ne_bot (P : W.Point) : pointIdeal P ≠ ⊥ := by
  cases P with
  | zero => exact top_ne_bot
  | some x y _ => exact EllipticCoordinateRing.XYIdeal_ne_bot x (C y)

open Classical in
/-- 有限個の点イデアルの積も零でない。後で生成元が非零であることを保証する。 -/
theorem prod_pointIdeal_ne_bot {ι : Type*} (s : Finset ι) (P : ι → W.Point) :
    (∏ i ∈ s, pointIdeal (P i)) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun i _ => pointIdeal_ne_bot (P i)

open Classical in
/-- Oを単位イデアルとして含む整数重み付きの主分数イデアル判定。 -/
theorem isPrincipal_prod_pointIdealUnit_zpow_iff {ι : Type*} (s : Finset ι)
    (P : ι → W.Point) (m : ι → ℤ) :
    ((∏ i ∈ s, pointIdealUnit (P i) ^ m i :
      (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
      Submodule W.CoordinateRing W.FunctionField).IsPrincipal ↔ ∑ i ∈ s, m i • P i = 0 := by
  rw [← ClassGroup.mk_eq_one_iff, ← Point.toClass_eq_zero, map_sum]
  have key : Additive.toMul (∑ i ∈ s, Point.toClass (m i • P i)) =
      ClassGroup.mk W.FunctionField (∏ i ∈ s, pointIdealUnit (P i) ^ m i) := by
    rw [map_prod, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zsmul, toMul_zsmul, map_zpow, toClass_eq_mk]
    rfl
  rw [← key]
  exact Additive.toMul.eq_symm_apply.symm

open Classical in
/-- 整イデアルの積が主であることと、同じ点の総和が零であることは同値である。
この橋は代数閉性も標数0も仮定せず、非特異点の群法とPoint.toClassの単射性から従う。 -/
theorem isPrincipal_prod_pointIdeal_iff {ι : Type*} (s : Finset ι) (P : ι → W.Point) :
    (∏ i ∈ s, pointIdeal (P i)).IsPrincipal ↔ ∑ i ∈ s, P i = 0 := by
  have h := isPrincipal_prod_pointIdealUnit_zpow_iff s P (fun _ => 1)
  simp only [zpow_one, one_smul] at h
  have hcoe : ((∏ i ∈ s, pointIdealUnit (P i) :
      (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      ((∏ i ∈ s, pointIdeal (P i) : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
    rw [Units.coe_prod]
    change _ = FractionalIdeal.coeIdealHom W.CoordinateRing⁰ W.FunctionField _
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => coe_pointIdealUnit (P i)
  rw [hcoe, FractionalIdeal.coe_coeIdeal] at h
  exact ((IsLocalization.coeSubmodule_isPrincipal _ le_rfl).symm).trans h

end DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
