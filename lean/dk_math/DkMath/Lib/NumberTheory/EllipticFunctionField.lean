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

import DkMath.Lib.NumberTheory.EllipticCoordinateRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Push

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionField"

/-!
# 関数体の一般点と、点への代入の引き戻し

座標環のX,Yの像を関数体へ入れ、曲線方程式を満たす実際の一般点を作る。
関数体値点への代入は常に座標環上で定義できるが、分数体への延長には単射性が必要である。
代数閉体上では、代入の核が非零ならその点は定数点となることを極大イデアルの分類から示せる。
従って定数点ではない点への代入は、分母を壊さず関数体へ延長できる。
Weil対やその非退化性はまだ構成しない。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.Point
variable {S : Type*} [CommRing S] {V : Affine S}

/-- 有限座標点のx座標。無限遠点では便宜的に0を返し、幾何学的な座標とは見なさない。 -/
def xc : V.Point → S
  | 0 => 0
  | some x _ _ => x

/-- 有限座標点のy座標。無限遠点での便宜的な値を使う際は非零条件を確認する。 -/
def yc : V.Point → S
  | 0 => 0
  | some _ y _ => y

/-- 非特異な有限点のx座標を取り出す。 -/
@[simp] lemma xc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).xc = x := rfl
/-- 非特異な有限点のy座標を取り出す。 -/
@[simp] lemma yc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).yc = y := rfl

/-- 非零点について、その座標の非特異性を取り出せる。 -/
lemma nonsingular_xc_yc {P : V.Point} (hP : P ≠ 0) : V.Nonsingular P.xc P.yc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

/-- 無限遠点以外の点を、座標と非特異性の証拠から再構成する。 -/
lemma eq_some_xc_yc {P : V.Point} (hP : P ≠ 0) : P = some P.xc P.yc (nonsingular_xc_yc hP) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

end WeierstrassCurve.Affine.Point

namespace DkMath.Lib.NumberTheory.EllipticFunctionField

section Generic

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

/-- 関数体上の点群の加法を扱うため、古典的な等号判定を固定する。 -/
noncomputable instance instDecidableEqFunctionField : DecidableEq (W⁄K).FunctionField :=
  Classical.decEq _

/-- 関数体内の一般点のx座標。座標環のXの実際の像である。 -/
noncomputable def genericX : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X))

/-- 関数体内の一般点のy座標。座標環のYの実際の像である。 -/
noncomputable def genericY : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) Y)

/-- 基底変換後の曲線方程式の評価を、元の係数の評価へ戻す。 -/
theorem evalEval_baseChange_polynomial (x y : (W⁄K).FunctionField) :
    (W⁄(W⁄K).FunctionField).polynomial.evalEval x y =
      (W⁄K).polynomial.eval₂ (aeval (R := K) x).toRingHom y := by
  rw [baseChange_polynomial W (Algebra.ofId K (W⁄K).FunctionField), evalEval, eval_map]
  have h := hom_eval₂ (W⁄K).polynomial (mapRingHom (Algebra.ofId K (W⁄K).FunctionField : K →+* _))
    (evalRingHom x) (C y)
  simp only [coe_evalRingHom, eval_C] at h
  rw [h]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, coe_evalRingHom,
      eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_evalRingHom,
      eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

/-- 座標環から関数体への写像は、Xを一般x座標に代入する写像と一致する。 -/
theorem algebraMap_comp_of :
    (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField).comp (AdjoinRoot.of (W⁄K).polynomial) =
      (aeval (R := K) (genericX W K)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_C]
    rw [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change (algebraMap K[X] (W⁄K).FunctionField) (algebraMap K K[X] c) = _
    exact (IsScalarTower.algebraMap_apply K K[X] (W⁄K).FunctionField c).symm
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X]
    rfl

/-- 一般座標は、関数体へ基底変換した曲線方程式を満たす。 -/
theorem generic_equation :
    (W⁄(W⁄K).FunctionField).Equation (genericX W K) (genericY W K) := by
  rw [Equation, evalEval_baseChange_polynomial, ← algebraMap_comp_of]
  have h0 := congrArg (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)
    (AdjoinRoot.eval₂_root (W⁄K).polynomial)
  rw [map_zero, hom_eval₂] at h0
  exact h0

/-- 楕円曲線性により、方程式を満たす一般点は非特異である。 -/
theorem generic_nonsingular [W.IsElliptic] :
    (W⁄(W⁄K).FunctionField).Nonsingular (genericX W K) (genericY W K) := by
  have : (W⁄(W⁄K).FunctionField).IsElliptic := by
    change (W.map (algebraMap R (W⁄K).FunctionField)).IsElliptic
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    exact W.isUnit_Δ.map _
  exact (equation_iff_nonsingular (W := W⁄(W⁄K).FunctionField)).mp (generic_equation W K)

/-- 曲線の関数体上の実際の一般点。非特異性の証拠も保持する。 -/
noncomputable def genericPoint [W.IsElliptic] : (W⁄(W⁄K).FunctionField).Point :=
  .some _ _ (generic_nonsingular W K)

/-- 一般点は有限点であり、群の零点である無限遠点とは異なる。 -/
theorem genericPoint_ne_zero [W.IsElliptic] : genericPoint W K ≠ 0 :=
  Point.some_ne_zero _

end Generic

section PointHom

variable {R : Type*} [Field R] {W : WeierstrassCurve R} {K : Type*} [Field K] [Algebra R K]

/-- 無限遠点以外の関数体値点の座標は、元の曲線方程式を消す。 -/
theorem eval₂_polynomial_of_point (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).polynomial.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc = 0 := by
  rw [← evalEval_baseChange_polynomial]
  exact (Point.nonsingular_xc_yc hQ).left

/-- 関数体値点への代入で定まる座標環の代数準同型。分数体への延長には単射性が必要。 -/
noncomputable def pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).CoordinateRing →ₐ[K] (W⁄K).FunctionField :=
  { AdjoinRoot.lift (aeval (R := K) Q.xc).toRingHom Q.yc (eval₂_polynomial_of_point Q hQ) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (Polynomial K) (W⁄K).CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.algebraMap_apply, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] }

/-- 多項式類への代入は、点の座標での多項式評価である。 -/
theorem pointHom_mk (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : (Polynomial K)[X]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) = g.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_point Q hQ) g

/-- 点への代入は係数を固定する。 -/
@[simp] theorem pointHom_mk_C_C (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (c : K) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C (C c))) = algebraMap K _ c :=
  (pointHom Q hQ).commutes c

/-- Xの類を代入すると、その点のx座標になる。 -/
@[simp] theorem pointHom_mk_C_X (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C X)) = Q.xc := by
  rw [pointHom_mk, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

/-- Yの類を代入すると、その点のy座標になる。 -/
@[simp] theorem pointHom_mk_Y (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) Y) = Q.yc := by
  rw [pointHom_mk, eval₂_X]

/-- 座標環の代数準同型は、XとYの二つの像だけで決まる。 -/
theorem coordinateRing_algHom_ext {A : Type*} [Semiring A] [Algebra K A]
    {f g : (W⁄K).CoordinateRing →ₐ[K] A}
    (hX : f (CoordinateRing.mk (W⁄K) (C X)) = g (CoordinateRing.mk (W⁄K) (C X)))
    (hY : f (CoordinateRing.mk (W⁄K) Y) = g (CoordinateRing.mk (W⁄K) Y)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change f (CoordinateRing.mk (W⁄K) (C q)) = g (CoordinateRing.mk (W⁄K) (C q))
    have hf : (f : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) =
        (g : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K _ c) = g (algebraMap K _ c)
        rw [AlgHom.commutes, AlgHom.commutes]
      · exact hX
    exact RingHom.congr_fun hf q
  · exact hY

/-- 一般点への代入は、座標環から関数体への標準の包含である。 -/
theorem pointHom_genericPoint [W.IsElliptic] :
    pointHom (genericPoint W K) (genericPoint_ne_zero W K) =
      IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField := by
  apply coordinateRing_algHom_ext
  · rw [pointHom_mk_C_X (W := W) (K := K), IsScalarTower.coe_toAlgHom', genericPoint, Point.xc_some]; rfl
  · rw [pointHom_mk_Y (W := W) (K := K), IsScalarTower.coe_toAlgHom', genericPoint, Point.yc_some]; rfl

/-- 点の写像のx座標は、係数写像を元のx座標へ適用したものである。 -/
theorem point_xc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).xc = f P.xc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

/-- 点の写像のy座標も係数写像と可換する。 -/
theorem point_yc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).yc = f P.yc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

/-- 代数閉体上で定数点ではない関数体値点への代入は単射である。非零核は点の極大イデアルになり、定数点へ戻ってしまう。 -/
theorem pointHom_injective_of_ne_baseChange [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hQK : ∀ P : (W⁄K).Point, Q ≠ Point.baseChange K (W⁄K).FunctionField P) :
    Function.Injective (pointHom Q hQ) := by
  rw [injective_iff_map_eq_zero]
  by_contra hcon
  push Not at hcon
  have hker : RingHom.ker (pointHom Q hQ) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := hcon
    intro h
    have hm : a ∈ RingHom.ker (pointHom Q hQ) := (RingHom.mem_ker).mpr ha
    rw [h, Ideal.mem_bot] at hm
    exact ha0 hm
  have : (RingHom.ker (pointHom Q hQ)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (pointHom Q hQ)).IsMaximal :=
    EllipticCoordinateRing.isMaximal_of_isPrime_of_ne_bot _ hker
  obtain ⟨a, b, hab, hker'⟩ := (EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal _).mp hmax
  have : (W⁄K).IsElliptic := by
    change (W.map (algebraMap R K)).IsElliptic
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    exact W.isUnit_Δ.map _
  have hns : (W⁄K).Nonsingular a b := (equation_iff_nonsingular (W := W⁄K)).mp hab
  have hx : Q.xc = algebraMap K _ a := by
    have : CoordinateRing.XClass (W⁄K) a ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert _ _)
    rw [RingHom.mem_ker, CoordinateRing.XClass, map_sub, map_sub, map_sub, pointHom_mk_C_X,
      pointHom_mk_C_C, sub_eq_zero] at this
    exact this
  have hy : Q.yc = algebraMap K _ b := by
    have : CoordinateRing.YClass (W⁄K) (C b) ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    rw [RingHom.mem_ker, CoordinateRing.YClass, map_sub, map_sub, pointHom_mk_Y, pointHom_mk_C_C,
      sub_eq_zero] at this
    exact this
  apply hQK (.some a b hns)
  rw [Point.eq_some_xc_yc hQ, Point.baseChange, Point.map_some]
  congr 1

/-- 単射な代入を分数体へ延長する。分母を非零に保つ仮定を隠さない。 -/
noncomputable def pointPull (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  IsFractionRing.liftAlgHom hinj

/-- 分数体へ延長しても、座標環の元への作用は元の代入に一致する。 -/
@[simp] theorem pointPull_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (h : (W⁄K).CoordinateRing) :
    pointPull Q hQ hinj (algebraMap _ _ h) = pointHom Q hQ h := by
  rw [pointPull, IsFractionRing.liftAlgHom_apply]
  exact IsFractionRing.lift_algebraMap hinj h

/-- 引き戻しで一般点を写すと、元の関数体値点が得られる。 -/
theorem map_pointPull_genericPoint [W.IsElliptic] (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    Point.map (pointPull Q hQ hinj) (genericPoint W K) = Q := by
  conv_rhs => rw [Point.eq_some_xc_yc hQ]
  rw [genericPoint, Point.map_some]
  congr 1
  · rw [genericX, pointPull_algebraMap, pointHom_mk_C_X]
  · rw [genericY, pointPull_algebraMap, pointHom_mk_Y]

/-- 引き戻しと点への代入の合成は、写した点への代入である。 -/
theorem pointPull_comp_pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (pointPull Q hQ hinj) P ≠ 0) :
    (pointPull Q hQ hinj).comp (pointHom P hP) = pointHom (Point.map (pointPull Q hQ hinj) P) hP' := by
  apply coordinateRing_algHom_ext
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, point_xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, point_yc_map]

/-- 等しい点への代入は等しい。非零性の証拠の選択には依存しない。 -/
theorem pointHom_congr {Q Q' : (W⁄(W⁄K).FunctionField).Point} (h : Q = Q') (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) :
    pointHom Q hQ = pointHom Q' hQ' := by subst h; rfl

/-- 引き戻しを座標環へ制限すると、元の点への代入になる。 -/
theorem pointPull_comp_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) = pointHom Q hQ :=
  RingHom.ext fun h => pointPull_algebraMap Q hQ hinj h

/-- 関数体の準同型は、座標環への制限で一意に決まる。 -/
theorem functionField_algHom_ext {φ ψ : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField}
    (h : (φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      (ψ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)) : φ = ψ :=
  AlgHom.coe_ringHom_injective
    (IsLocalization.ringHom_ext (nonZeroDivisors (W⁄K).CoordinateRing) h)
end PointHom

end DkMath.Lib.NumberTheory.EllipticFunctionField
