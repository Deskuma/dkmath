/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_FunctionFieldPullback.lean.
Upstream blob: ce8783a9e9613db1c4c0323ce93fb0d89917ee65
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldNegation"

/-!
# 関数体の反転作用

一般点の群法による反転を、単射な座標代入から関数体の自己同型へ持ち上げる。
反転はxを固定しyを変える。この差が、後続の次数評価で余分な二次拡大を排除する。
-/

namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [IsAlgClosed K] [W.IsElliptic]

omit [IsAlgClosed K] in
open Classical in
/-- 一般点の反転も定数点にはならない。 -/
theorem neg_genericPoint_ne_baseChange (P : (W⁄K).Point) :
    -genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  apply genericPoint_ne_baseChange W K (-P)
  rw [map_neg, ← h, neg_neg]

open Classical in
/-- 反転した一般点への代入は単射であり、分母を保つ。 -/
theorem negHom_injective :
    Function.Injective (pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _))) := by
  classical
  exact pointHom_injective_of_ne_baseChange _ _ (neg_genericPoint_ne_baseChange W K)

open Classical in
/-- 群の反転による関数の引き戻し。 -/
noncomputable def negPull : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (neg_ne_zero.mpr (Point.some_ne_zero _)) (negHom_injective W K)

open Classical in
/-- 反転の引き戻しは一般点を負の点へ移す。 -/
theorem map_negPull_genericPoint : Point.map (negPull W K) (genericPoint W K) = -genericPoint W K :=
  map_pointPull_genericPoint _ _ _

open Classical in
/-- 座標環上では反転点への代入である。 -/
theorem negPull_algebraMap (g : (W⁄K).CoordinateRing) :
    negPull W K (algebraMap _ _ g) = pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _)) g :=
  pointPull_algebraMap _ _ _ g

open Classical in
/-- 反転引き戻しと座標環の包含は可換である。 -/
theorem negPull_comp_algebraMap :
    (negPull W K : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _)) :=
  pointPull_comp_algebraMap _ _ _

open Classical in
/-- 反転引き戻しと点への代入の合成を計算する。 -/
theorem negPull_comp_pointHom (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (negPull W K) P ≠ 0) :
    (negPull W K).comp (pointHom P hP) = pointHom (Point.map (negPull W K) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

open Classical in
/-- 二度の反転は恒等写像となる。 -/
theorem negPull_comp_negPull : (negPull W K).comp (negPull W K) = AlgHom.id K _ := by
  apply functionField_algHom_ext
  have hP' : Point.map (negPull W K) (-genericPoint W K) = genericPoint W K := by
    rw [map_neg, map_negPull_genericPoint, neg_neg]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, negPull_comp_algebraMap, ← AlgHom.comp_toRingHom,
    negPull_comp_pointHom W K _ _ (by rw [hP']; exact Point.some_ne_zero _),
    pointHom_congr hP' _ (Point.some_ne_zero _), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

open Classical in
/-- 反転を、実際の関数体の代数自己同型へまとめる。 -/
noncomputable def negEquiv : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (negPull W K) (negPull W K) (negPull_comp_negPull W K) (negPull_comp_negPull W K)

open Classical in
/-- 自己同型を準同型として見ても同じ引き戻しである。 -/
theorem coe_negEquiv : (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = negPull W K := rfl

open Classical in
/-- 自己同型の作用は反転引き戻しそのものである。 -/
theorem negEquiv_apply (h : (W⁄K).FunctionField) : negEquiv W K h = negPull W K h := rfl

open Classical in
/-- 反転自己同型による一般点の像。 -/
theorem map_negEquiv_genericPoint :
    Point.map (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K) =
      -genericPoint W K := by
  rw [coe_negEquiv, map_negPull_genericPoint]

open Classical in
/-- 反転はx座標を固定する。 -/
theorem negEquiv_genericX : negEquiv W K (genericX W K) = genericX W K := by
  rw [negEquiv_apply, genericX, negPull_algebraMap, pointHom_mk_C_X]
  simp only [genericPoint, Point.neg_some, Point.xc_some]
  rfl

open Classical in
/-- 反転はy座標を曲線のnegYへ移す。 -/
theorem negEquiv_genericY :
    negEquiv W K (genericY W K) = (W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) := by
  rw [negEquiv_apply, genericY, negPull_algebraMap, pointHom_mk_Y]
  simp only [genericPoint, Point.neg_some, Point.yc_some]
  rfl

open Classical in
/-- 反転自己同型は自分自身を逆写像とする。 -/
theorem negEquiv_symm : (negEquiv W K).symm = negEquiv W K := rfl


end DkMath.Lib.NumberTheory.EllipticFunctionField
