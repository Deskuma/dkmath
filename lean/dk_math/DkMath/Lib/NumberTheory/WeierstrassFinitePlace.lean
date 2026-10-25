/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces and EllipticValuationTransport,
originally Definitions/Def_EllipticCurve_FunctionFieldPullback.lean,
blob ce8783a9e9613db1c4c0323ce93fb0d89917ee65.
Modified: a point on the actual target model, with no extra base change of its coefficient field.
-/

import DkMath.Lib.NumberTheory.EllipticInfinityValuation
import DkMath.Lib.NumberTheory.DiscreteValuationPullback
import DkMath.Lib.NumberTheory.WeierstrassCoordinateEvaluation

#print "file: DkMath.Lib.NumberTheory.WeierstrassFinitePlace"

/-!
# 同じモデルの有限点と、その場所での座標代入

[DkMath.Lib] 標的が既に代数閉包係数であっても、係数体の再度の基底変換を挟まない。
実際のモデルの座標環・関数体上に有限点の場所を構成する。
座標の剰余合同から、座標環全体の合同と、その点の零点イデアルとの整合を得る。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassFinitePlace
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCoordinateEvaluation
open scoped Polynomial.Bivariate
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- [DkMath.Lib] 有限点の座標差の素イデアル。無限遠点には適用しない。 -/
noncomputable def finitePlace (P : W.toAffine.Point) (hP : P ≠ 0) :
    HeightOneSpectrum W.toAffine.CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal W.toAffine P.xc (C P.yc)
  isPrime := (EllipticCoordinateRing.isMaximal_XYIdeal (Point.nonsingular_xc_yc hP).left).isPrime
  ne_bot h := CoordinateRing.XClass_ne_zero (W' := W.toAffine) P.xc
    (by rw [← Ideal.mem_bot, ← h]; exact Ideal.subset_span (Set.mem_insert _ _))

/-- [DkMath.Lib] 同じ有限点での座標環評価。分数体全体の評価ではない。 -/
noncomputable def finiteEval (P : W.toAffine.Point) (hP : P ≠ 0) :
    W.toAffine.CoordinateRing →+* k := AdjoinRoot.evalEval (Point.nonsingular_xc_yc hP).left

/-- [DkMath.Lib] 座標環の多項式類を、同じ有限点で二段評価する。 -/
theorem finiteEval_mk (P : W.toAffine.Point) (hP : P ≠ 0) (g : k[X][X]) :
    finiteEval W P hP (CoordinateRing.mk W.toAffine g) = g.evalEval P.xc P.yc :=
  AdjoinRoot.evalEval_mk _ _

/-- [DkMath.Lib] 座標差イデアルの元は同じ点で消える。 -/
theorem finiteEval_of_mem (P : W.toAffine.Point) (hP : P ≠ 0) :
    ∀ b ∈ (finitePlace W P hP).asIdeal, finiteEval W P hP b = 0 := by
  intro b hb
  rw [← RingHom.mem_ker]
  revert hb b
  rw [← SetLike.le_def]
  change CoordinateRing.XYIdeal W.toAffine P.xc (C P.yc) ≤ _
  rw [CoordinateRing.XYIdeal, Ideal.span_le]
  rintro b (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.XClass, finiteEval_mk,
      evalEval_C, eval_sub, eval_X, eval_C, sub_self]
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.YClass, finiteEval_mk,
      evalEval_sub, evalEval_X, evalEval_C, eval_C, sub_self]

/-- [DkMath.Lib] 有限点の素イデアルは評価準同型の核と正確に一致する。 -/
theorem mem_finitePlace_iff (P : W.toAffine.Point) (hP : P ≠ 0)
    (b : W.toAffine.CoordinateRing) :
    b ∈ (finitePlace W P hP).asIdeal ↔ finiteEval W P hP b = 0 := by
  have he : (finitePlace W P hP).asIdeal = RingHom.ker (finiteEval W P hP) := by
    apply (EllipticCoordinateRing.isMaximal_XYIdeal (Point.nonsingular_xc_yc hP).left).eq_of_le
      (RingHom.ker_ne_top _)
    intro a ha
    exact (RingHom.mem_ker).mpr (finiteEval_of_mem W P hP a ha)
  rw [he, RingHom.mem_ker]

/-- [DkMath.Lib] 係数体を再度拡大せず、同じ楕円モデルの全点に正規化付値を割り当てる。
Oはノルム次数による無限遠付値、有限点は同じ座標差素イデアルの離散付値である。 -/
noncomputable def modelPointValuation [IsAlgClosed k] [W.IsElliptic] (P : W.toAffine.Point) :
    Valuation W.toAffine.FunctionField ℤᵐ⁰ := by
  classical
  let : IsDedekindDomain W.toAffine.CoordinateRing := EllipticCoordinateRing.isDedekindDomain
  exact if hP : P = 0 then EllipticInfinityValuation.valuationInfty W.toAffine
    else (finitePlace W P hP).valuation _

/-- [DkMath.Lib] 同じモデルのOには、既存の無限遠付値そのものを割り当てる。 -/
theorem modelPointValuation_zero [IsAlgClosed k] [W.IsElliptic] :
    modelPointValuation W 0 = EllipticInfinityValuation.valuationInfty W.toAffine := by
  classical
  simp [modelPointValuation]

/-- [DkMath.Lib] 有限点では、その点の素イデアルから作った付値を使う。 -/
theorem modelPointValuation_of_ne_zero [IsAlgClosed k] [W.IsElliptic]
    [IsDedekindDomain W.toAffine.CoordinateRing] (P : W.toAffine.Point) (hP : P ≠ 0) :
    modelPointValuation W P = (finitePlace W P hP).valuation W.toAffine.FunctionField := by
  classical
  simp only [modelPointValuation, dite_eq_right hP]

variable {F : Type*} [Field F] [Algebra k F] (v : Valuation F ℤᵐ⁰)

/-- [DkMath.Lib] 代入する二座標が有限点に合同なら、全ての座標環元の評価も合同。
分母のない段階なので、正則性は合同の定数側から内部供給する。 -/
theorem coordinateEval_congr (x y : F) (hxy : (W.toAffine⁄F).Equation x y)
    (P : W.toAffine.Point) (hP : P ≠ 0)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1)
    (hx : v.Cong x (algebraMap k F P.xc)) (hy : v.Cong y (algebraMap k F P.yc))
    (b : W.toAffine.CoordinateRing) :
    v.Cong (coordinateEval W x y hxy b) (algebraMap k F (finiteEval W P hP b)) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  change v.Cong (coordinateEval W x y hxy (CoordinateRing.mk W.toAffine g))
    (algebraMap k F (finiteEval W P hP (CoordinateRing.mk W.toAffine g)))
  rw [coordinateEval_mk, finiteEval_mk]
  have hm : algebraMap k F (g.evalEval P.xc P.yc) =
      g.eval₂ (eval₂RingHom (algebraMap k F) (algebraMap k F P.xc)) (algebraMap k F P.yc) := by
    have he : (algebraMap k F).comp (evalEvalRingHom P.xc P.yc) =
        eval₂RingHom (eval₂RingHom (algebraMap k F) (algebraMap k F P.xc))
          (algebraMap k F P.yc) := by
      apply Polynomial.ringHom_ext
      · intro q
        simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C,
          coe_eval₂RingHom, eval₂_C, eval₂_at_apply]
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X,
          eval_C, coe_eval₂RingHom, eval₂_X]
    exact RingHom.congr_fun he g
  rw [hm]
  exact (Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap k F) hc hx (hc _) hy (hc _) g).1

/-- [DkMath.Lib] 同じ座標代入の局所中心は有限点P。消える元と単元を同時に識別する。 -/
theorem coordinateEval_center (x y : F) (hxy : (W.toAffine⁄F).Equation x y)
    (P : W.toAffine.Point) (hP : P ≠ 0)
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (hx : v.Cong x (algebraMap k F P.xc)) (hy : v.Cong y (algebraMap k F P.yc)) :
    (∀ b ∈ (finitePlace W P hP).asIdeal, v (coordinateEval W x y hxy b) ≤ exp (-1 : ℤ)) ∧
    (∀ b ∉ (finitePlace W P hP).asIdeal, v (coordinateEval W x y hxy b) = 1) := by
  have hc₀ (c : k) : v (algebraMap k F c) ≤ 1 := by
    by_cases h : c = 0
    · simp [h]
    · exact (hc c h).le
  constructor
  · intro b hb
    have h := coordinateEval_congr W v x y hxy P hP hc₀ hx hy b
    rw [finiteEval_of_mem W P hP b hb, map_zero, Valuation.cong_zero_iff] at h
    exact WithZero.lt_one_iff_le_exp_neg_one.mp h
  · intro b hb
    have h := coordinateEval_congr W v x y hxy P hP hc₀ hx hy b
    exact h.eq_of_eq_one (hc _ (fun hz => hb ((mem_finitePlace_iff W P hP b).mpr hz)))

end DkMath.Lib.NumberTheory.WeierstrassFinitePlace
