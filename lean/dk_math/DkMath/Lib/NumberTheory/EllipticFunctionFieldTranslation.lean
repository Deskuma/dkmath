/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_FunctionFieldPullback.lean.
Upstream blob: ce8783a9e9613db1c4c0323ce93fb0d89917ee65
Modified for DkMath: use proved coordinate-ideal classification,
separate generic-point substitution from translations and valuation transport,
and add textbook documentation.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionField

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation"

/-!
# 平行移動による関数体の自己同型

楕円曲線の群法を一般点へ適用し、有理関数の引き戻しを構成する。
座標環での単射性、分数体への延長、逆の移動、合成則、作用の忠実性までを証明する。
移動によって有限点に極が現れ得るため、自己同型の対象は関数体である。
これはWeil対の関数を移動するための土台であり、対の存在や非退化性は主張しない。
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace DkMath.Lib.NumberTheory.EllipticFunctionField

section Translation

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

omit [IsAlgClosed K] in
/-- 一般点は定数点ではない。Xの座標環内での非零性がこの差を検出する。 -/
theorem genericPoint_ne_baseChange (P : (W⁄K).Point) :
    genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  cases P with
  | zero => exact Point.some_ne_zero _ (h.trans (map_zero _))
  | some a b hab =>
    rw [genericPoint, Point.baseChange, Point.map_some, Point.some.injEq] at h
    apply CoordinateRing.XClass_ne_zero (W' := W⁄K) a
    apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
    rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero]
    have h1 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X)) =
        genericX W K := rfl
    have h2 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C (C a))) =
        algebraMap K (W⁄K).FunctionField a :=
      (IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField a).symm
    rw [h1, h2, h.1, sub_eq_zero]
    rfl

omit [IsAlgClosed K] in
/-- 一般点に定数点を加えても無限遠点にならない。 -/
theorem genericPoint_add_baseChange_ne_zero (S : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ 0 := by
  intro h
  apply genericPoint_ne_baseChange W K (-S)
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

omit [IsAlgClosed K] in
/-- 平行移動された一般点も定数点ではない。 -/
theorem genericPoint_add_baseChange_ne_baseChange (S P : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ Point.baseChange K _ P := by
  intro h
  apply genericPoint_ne_baseChange W K (P - S)
  rw [map_sub, ← h, add_sub_cancel_right]

/-- 非定数性と極大イデアルの分類から、平行移動による座標代入は単射である。 -/
theorem transHom_injective (S : (W⁄K).Point) :
    Function.Injective (pointHom (genericPoint W K + Point.baseChange K _ S)
      (genericPoint_add_baseChange_ne_zero W K S)) :=
  pointHom_injective_of_ne_baseChange _ _ (genericPoint_add_baseChange_ne_baseChange W K S)

/-- 平行移動による有理関数の引き戻し。単射な座標代入を分数体へ延長する。 -/
noncomputable def transPull (S : (W⁄K).Point) : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

/-- 引き戻しは一般点を実際の群法による和へ移す。 -/
theorem map_transPull_genericPoint (S : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K) = genericPoint W K + Point.baseChange K _ S :=
  map_pointPull_genericPoint _ _ _

/-- 定数点は係数体上の写像で固定され、二つの平行移動は加法に従う。 -/
theorem map_transPull_genericPoint_add (S T : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K + Point.baseChange K _ T) =
      genericPoint W K + Point.baseChange K _ (S + T) := by
  rw [map_add, map_transPull_genericPoint, Point.map_baseChange, add_assoc, ← map_add]

/-- 平行移動を座標環に制限すると、移動先の一般点への代入になる。 -/
theorem transPull_comp_algebraMap (S : (W⁄K).Point) :
    (transPull W K S : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (genericPoint W K + Point.baseChange K _ S) (genericPoint_add_baseChange_ne_zero W K S) :=
  pointPull_comp_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

/-- 平行移動と点への代入の合成は、点を移してからの代入に一致する。 -/
theorem transPull_comp_pointHom (S : (W⁄K).Point) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (transPull W K S) P ≠ 0) :
    (transPull W K S).comp (pointHom P hP) = pointHom (Point.map (transPull W K S) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

/-- 二つの座標代入の合成を、点群の和で計算する。 -/
theorem transPull_comp_transHom (S T : (W⁄K).Point) :
    (transPull W K S).comp (pointHom (genericPoint W K + Point.baseChange K _ T)
      (genericPoint_add_baseChange_ne_zero W K T)) =
      pointHom (genericPoint W K + Point.baseChange K _ (S + T))
        (genericPoint_add_baseChange_ne_zero W K (S + T)) := by
  apply coordinateRing_algHom_ext
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, ← map_transPull_genericPoint_add,
      point_xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, ← map_transPull_genericPoint_add,
      point_yc_map]

/-- 有理関数上の平行移動の合成則。分数体の普遍性で座標上の等式から延長する。 -/
theorem transPull_comp (S T : (W⁄K).Point) :
    (transPull W K S).comp (transPull W K T) = transPull W K (S + T) := by
  apply functionField_algHom_ext
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, transPull_comp_algebraMap W K T,
    transPull_comp_algebraMap W K (S + T), ← AlgHom.comp_toRingHom, transPull_comp_transHom]

/-- 零点による平行移動は恒等写像である。 -/
theorem transPull_zero : transPull W K 0 = AlgHom.id K _ := by
  apply functionField_algHom_ext
  rw [transPull_comp_algebraMap]
  have h0 : genericPoint W K + Point.baseChange K (W⁄K).FunctionField (0 : (W⁄K).Point) =
      genericPoint W K := by
    rw [map_zero, add_zero]
  rw [pointHom_congr h0 _ (genericPoint_ne_zero W K), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

/-- 負の点による移動を逆写像とする、実際の関数体の代数自己同型。 -/
noncomputable def transEquiv (S : (W⁄K).Point) : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (transPull W K S) (transPull W K (-S))
    (by rw [transPull_comp, add_neg_cancel, transPull_zero])
    (by rw [transPull_comp, neg_add_cancel, transPull_zero])

/-- 代数同型の作用は構成に用いた引き戻しそのものである。 -/
theorem transEquiv_apply (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    transEquiv W K S h = transPull W K S h := rfl

/-- 代数同型を準同型として見たときの同一性。 -/
theorem coe_transEquiv (S : (W⁄K).Point) :
    (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = transPull W K S := rfl

/-- 座標環から来る関数への作用は、移動後の一般点で評価できる。 -/
theorem transEquiv_algebraMap (S : (W⁄K).Point) (h : (W⁄K).CoordinateRing) :
    transEquiv W K S (algebraMap _ _ h) =
      pointHom (genericPoint W K + Point.baseChange K _ S) (genericPoint_add_baseChange_ne_zero W K S) h :=
  pointPull_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S) h

/-- 一般x座標への作用を移動先の点のx座標で記述する。 -/
theorem transEquiv_genericX (S : (W⁄K).Point) :
    transEquiv W K S (genericX W K) = (genericPoint W K + Point.baseChange K _ S).xc := by
  rw [genericX, transEquiv_algebraMap, pointHom_mk_C_X]

/-- 一般y座標への作用を移動先の点のy座標で記述する。 -/
theorem transEquiv_genericY (S : (W⁄K).Point) :
    transEquiv W K S (genericY W K) = (genericPoint W K + Point.baseChange K _ S).yc := by
  rw [genericY, transEquiv_algebraMap, pointHom_mk_Y]

/-- 自己同型を点に作用させると、一般点は指定した点だけ移動する。 -/
theorem map_transEquiv_genericPoint (S : (W⁄K).Point) :
    Point.map (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K) =
      genericPoint W K + Point.baseChange K _ S := by
  rw [coe_transEquiv, map_transPull_genericPoint]

/-- 平行移動の和と自己同型の合成。AlgEquiv.transの適用順序を明示する。 -/
theorem transEquiv_add (S T : (W⁄K).Point) :
    transEquiv W K (S + T) = (transEquiv W K T).trans (transEquiv W K S) := by
  apply AlgEquiv.ext
  intro h
  rw [AlgEquiv.trans_apply, transEquiv_apply, transEquiv_apply, transEquiv_apply,
    ← AlgHom.comp_apply, transPull_comp]

/-- 零点による自己同型は恒等同型である。 -/
theorem transEquiv_zero : transEquiv W K 0 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro h
  rw [transEquiv_apply, transPull_zero]
  rfl

/-- 作用の忠実性。二つの座標への作用が等しければ、一般点を消去して移動量も等しい。 -/
theorem transEquiv_injective : Function.Injective (transEquiv W K) := by
  intro S T h
  have hx := transEquiv_genericX W K S
  have hy := transEquiv_genericY W K S
  rw [h, transEquiv_genericX] at hx
  rw [h, transEquiv_genericY] at hy
  have hpt : genericPoint W K + Point.baseChange K _ T = genericPoint W K + Point.baseChange K _ S := by
    rw [Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K T),
      Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K S)]
    congr 1
  exact (Point.map_injective _ (add_left_cancel hpt)).symm

end Translation

end DkMath.Lib.NumberTheory.EllipticFunctionField
