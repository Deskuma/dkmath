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
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces"

/-!
# 有限点と座標環の非零素イデアル

点での有理関数の零・極を論じるには、点を付値の場所へ結び付ける必要がある。
ここではその前段として、有限点とHeightOneSpectrumの対応を証明する。
座標環のDedekind性と組み合わせて局所付値を導入する入口になる。
無限遠点の付値、移動による付値輸送、Weil関数の因子はまだ扱わない。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace DkMath.Lib.NumberTheory.EllipticFunctionField

section Places

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

/-- 有限点を、その座標差で生成される非零素イデアルへ送る。無限遠点はこのアフィン座標環には現れない。 -/
noncomputable def placeOf (P : (W⁄K).Point) (hP : P ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc)
  isPrime := (EllipticCoordinateRing.isMaximal_XYIdeal (Point.nonsingular_xc_yc hP).left).isPrime
  ne_bot h := CoordinateRing.XClass_ne_zero (W' := W⁄K) P.xc
    (by rw [← Ideal.mem_bot, ← h]; exact Ideal.subset_span (Set.mem_insert _ _))

omit [DecidableEq K] in
/-- 有限点に対応する素イデアルの具体的な生成元。 -/
@[simp] theorem placeOf_asIdeal (P : (W⁄K).Point) (hP : P ≠ 0) :
    (placeOf W K P hP).asIdeal = CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) := rfl

omit [DecidableEq K] in
/-- 代数閉体上の全ての非零素イデアルは有限点から得られる。 -/
theorem placeOf_surjective [IsAlgClosed K] [W.IsElliptic]
    (v : IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing) :
    ∃ (P : (W⁄K).Point) (hP : P ≠ 0), placeOf W K P hP = v := by
  have : (W⁄K).IsElliptic := by
    change (W.map (algebraMap R K)).IsElliptic
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    exact W.isUnit_Δ.map _
  have := v.isPrime
  obtain ⟨a, b, hab, hv⟩ := (EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal v.asIdeal).mp
    (EllipticCoordinateRing.isMaximal_of_isPrime_of_ne_bot v.asIdeal v.ne_bot)
  refine ⟨.some a b ((equation_iff_nonsingular (W := W⁄K)).mp hab), Point.some_ne_zero _, ?_⟩
  exact IsDedekindDomain.HeightOneSpectrum.ext hv.symm

/-- 曲線方程式を満たす点での座標環の評価準同型。関数体全体では分母の零点が障害となる。 -/
noncomputable def evalAt {a b : K} (h : (W⁄K).Equation a b) : (W⁄K).CoordinateRing →+* K :=
  AdjoinRoot.evalEval h

omit [DecidableEq K] in
/-- 座標環の評価を二変数多項式の代入へ戻す。 -/
theorem evalAt_mk {a b : K} (h : (W⁄K).Equation a b) (g : K[X][Y]) :
    evalAt W K h (CoordinateRing.mk (W⁄K) g) = g.evalEval a b :=
  AdjoinRoot.evalEval_mk h g

omit [DecidableEq K] in
/-- 点で消える座標差のイデアル全体は、点での評価の核に入る。 -/
theorem evalAt_XYIdeal {a b : K} (h : (W⁄K).Equation a b) :
    ∀ g ∈ CoordinateRing.XYIdeal (W⁄K) a (C b), evalAt W K h g = 0 := by
  intro g hg
  rw [← RingHom.mem_ker]
  revert hg g
  rw [← SetLike.le_def, CoordinateRing.XYIdeal, Ideal.span_le]
  rintro g (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.XClass, evalAt_mk,
      evalEval_C, eval_sub, eval_X, eval_C, sub_self]
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.YClass, evalAt_mk,
      evalEval_sub, evalEval_X, evalEval_C, eval_C, sub_self]

omit [DecidableEq K] in
/-- 二つの有限点のイデアルが等しければ、座標差を評価して両座標の一致が分かる。 -/
theorem placeOf_injective {P Q : (W⁄K).Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : placeOf W K P hP = placeOf W K Q hQ) : P = Q := by
  have hI : CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) = CoordinateRing.XYIdeal (W⁄K) Q.xc (C Q.yc) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  have hev := evalAt_XYIdeal W K (Point.nonsingular_xc_yc hP).left
  rw [hI] at hev
  have hx : P.xc = Q.xc := by
    have := hev _ (Ideal.subset_span (Set.mem_insert _ _))
    rw [CoordinateRing.XClass, evalAt_mk, evalEval_C, eval_sub, eval_X, eval_C,
      sub_eq_zero] at this
    exact this
  have hy : P.yc = Q.yc := by
    have := hev _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [CoordinateRing.YClass, evalAt_mk, evalEval_sub, evalEval_X, evalEval_C, eval_C,
      sub_eq_zero] at this
    exact this
  rw [Point.eq_some_xc_yc hP, Point.eq_some_xc_yc hQ]
  congr 1

end Places

end DkMath.Lib.NumberTheory.EllipticFunctionField
