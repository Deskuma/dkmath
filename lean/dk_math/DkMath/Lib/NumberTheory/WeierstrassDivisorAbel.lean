/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.DedekindFractionalValuation
import DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
import DkMath.Lib.NumberTheory.WeierstrassFinitePlace
import DkMath.Lib.NumberTheory.ValuationDivisor

#print "file: DkMath.Lib.NumberTheory.WeierstrassDivisorAbel"

/-!
# 無限遠係数の補正を許した、点の総和と主因子のAbel対応

[DkMath.Lib] 有限点の零・極の整数重みを可逆分数イデアルの積に戻す。
主分数イデアルの指数は同じ関数の有限付値であり、Point.toClassの単射性が
「主因子の点の総和はO」を与える。逆向きはOの係数を一つ補正すれば成立する。

これは次数0のPicard群の全構成を要求しないアフィンAbel対応である。
補正係数が元の次数の負であるという積公式は主張しない。
OをOへ送る点関数の加法性には、Oの寄与が点の総和で消えるので、この形で十分となる。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassDivisorAbel
open WeierstrassCurve WeierstrassCurve.Affine WithZero Polynomial
open IsDedekindDomain EllipticPrincipalPointIdeal WeierstrassFinitePlace
open scoped nonZeroDivisors BigOperators
variable {k : Type*} [Field k] (W : WeierstrassCurve k)
noncomputable local instance instDecidableEqWeierstrassDivisorAbel {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 有限支持因子の整数重み付きの、実際の点群での総和。 -/
noncomputable def pointSum : (W.toAffine.Point →₀ ℤ) →+ W.toAffine.Point where
  toFun D := D.sum (fun P n => n • P)
  map_zero' := by simp
  map_add' D C := Finsupp.sum_add_index' (fun _ => zero_zsmul _) (fun _ _ _ => add_zsmul _ _ _)

/-- [DkMath.Lib] 一点の重みは、その点の整数倍として総和に寄与する。 -/
theorem pointSum_single (P : W.toAffine.Point) (n : ℤ) :
    pointSum W (Finsupp.single P n) = n • P := by
  change (Finsupp.single P n).sum (fun P n => n • P) = _
  exact Finsupp.sum_single_index (zero_zsmul P)

/-- [DkMath.Lib] 点差の因子[P]−[O]の総和はPである。 -/
theorem pointSum_pointDivisor (P : W.toAffine.Point) :
    pointSum W (Finsupp.single P 1 - Finsupp.single 0 1) = P := by
  rw [map_sub, pointSum_single, pointSum_single]
  simp

/-- [DkMath.Lib] 有限点のイデアルの同一性から、同じ点を復元する。 -/
theorem finitePlace_injective {P Q : W.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : finitePlace W P hP = finitePlace W Q hQ) : P = Q := by
  apply Point.toClass_injective
  rw [toClass_eq_mk, toClass_eq_mk]
  apply congrArg (ClassGroup.mk W.toAffine.FunctionField)
  apply Units.ext
  rw [coe_pointIdealUnit, coe_pointIdealUnit, pointIdeal_of_ne_zero hP, pointIdeal_of_ne_zero hQ]
  exact congrArg (fun v : HeightOneSpectrum W.toAffine.CoordinateRing =>
    (v.asIdeal : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)) h

/-- [DkMath.Lib] 代数閉体上の同じモデルでは、全アフィン素点は非零点から得られる。 -/
theorem finitePlace_surjective [IsAlgClosed k] [W.IsElliptic]
    (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    ∃ (P : W.toAffine.Point) (hP : P ≠ 0), finitePlace W P hP = v := by
  have := v.isPrime
  obtain ⟨a, b, hab, hv⟩ := (EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal v.asIdeal).mp
    (EllipticCoordinateRing.isMaximal_of_isPrime_of_ne_bot v.asIdeal v.ne_bot)
  refine ⟨.some a b ((equation_iff_nonsingular (W := W.toAffine)).mp hab), Point.some_ne_zero _, ?_⟩
  exact HeightOneSpectrum.ext hv.symm

/-- [DkMath.Lib] 因子の整数重みに対応する、可逆な点イデアルの積。Oの因子は単位元。 -/
noncomputable def pointIdealProduct (D : W.toAffine.Point →₀ ℤ) :
    (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ :=
  D.prod (fun P n => pointIdealUnit P ^ n)

/-- [DkMath.Lib] 同じ点イデアル積が主であることと、点の総和がOであることは同値。 -/
theorem pointIdealProduct_isPrincipal_iff (D : W.toAffine.Point →₀ ℤ) :
    ((pointIdealProduct W D : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) :
      Submodule W.toAffine.CoordinateRing W.toAffine.FunctionField).IsPrincipal ↔ pointSum W D = 0 :=
  isPrincipal_prod_pointIdealUnit_zpow_iff D.support id D

variable [IsAlgClosed k] [W.IsElliptic]
local instance : IsDedekindDomain W.toAffine.CoordinateRing := EllipticCoordinateRing.isDedekindDomain

/-- [DkMath.Lib] 同じ有限点で点イデアルを測ると、一致する点のみ指数1を持つ。 -/
theorem count_pointIdealUnit (P : W.toAffine.Point) (hP : P ≠ 0) (Q : W.toAffine.Point) :
    FractionalIdeal.count W.toAffine.FunctionField (finitePlace W P hP)
      (pointIdealUnit Q : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
        if Q = P then 1 else 0 := by
  by_cases hQ : Q = 0
  · subst Q
    change FractionalIdeal.count _ _ 1 = _
    rw [FractionalIdeal.count_one, ite_eq_right (Ne.symm hP)]
  · rw [coe_pointIdealUnit, pointIdeal_of_ne_zero hQ]
    change FractionalIdeal.count _ _ ((finitePlace W Q hQ).asIdeal :
      FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = _
    rw [FractionalIdeal.count_maximal]
    congr 1
    exact propext ⟨finitePlace_injective W hQ hP, fun h => by subst Q; rfl⟩

/-- [DkMath.Lib] 点イデアル積の同じ有限素点での指数は、元の因子の係数そのもの。 -/
theorem count_pointIdealProduct (D : W.toAffine.Point →₀ ℤ) (P : W.toAffine.Point) (hP : P ≠ 0) :
    FractionalIdeal.count W.toAffine.FunctionField (finitePlace W P hP)
      (pointIdealProduct W D : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = D P := by
  unfold pointIdealProduct Finsupp.prod
  rw [Units.coe_prod, FractionalIdeal.count_prod]
  · simp_rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow, count_pointIdealUnit W P hP,
      mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
    split_ifs with h
    · exact h.symm
    · rfl
  · intro Q _
    exact Units.ne_zero _

/-- [DkMath.Lib] 同じ関数fの有限付値を持つ因子は、主分数イデアル(f)を再現する。
全アフィン素点を有限点に戻してから、Dedekind分解の一意性を使う。 -/
theorem pointIdealProduct_eq_span_of_finite_orders (D : W.toAffine.Point →₀ ℤ)
    (f : W.toAffine.FunctionField) (hf : f ≠ 0)
    (hD : ∀ (P : W.toAffine.Point) (hP : P ≠ 0),
      D P = -log ((finitePlace W P hP).valuation W.toAffine.FunctionField f)) :
    (pointIdealProduct W D : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
      FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f := by
  apply DedekindFractionalValuation.ext_count (Units.ne_zero _)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf)
  intro v
  obtain ⟨P, hP, rfl⟩ := finitePlace_surjective W v
  rw [count_pointIdealProduct, DedekindFractionalValuation.count_spanSingleton _ _ hf, hD P hP]

/-- [DkMath.Lib] 全点の正規化付値による主因子の点の総和はOとなる。
Oは点の総和で零なので、主分数イデアルの有限素点での分解だけで証明できる。 -/
theorem pointSum_eq_zero_of_isPrincipal (D : W.toAffine.Point →₀ ℤ)
    (hD : ValuationDivisor.IsPrincipal (modelPointValuation W) D) : pointSum W D = 0 := by
  obtain ⟨f, hf, hD⟩ := hD
  apply (pointIdealProduct_isPrincipal_iff W D).mp
  apply (FractionalIdeal.isPrincipal_iff _).mpr
  refine ⟨f, pointIdealProduct_eq_span_of_finite_orders W D f hf (fun P hP => ?_)⟩
  rw [← modelPointValuation_of_ne_zero W P hP]
  exact hD P

/-- [DkMath.Lib] 点の総和がOなら、Oの整数係数を一つ補正して実際の主因子を得る。
補正値は選んだ同じ生成関数の無限遠位数から定め、積公式は仮定しない。 -/
theorem exists_principal_correction (D : W.toAffine.Point →₀ ℤ) (hD : pointSum W D = 0) :
    ∃ n : ℤ, ValuationDivisor.IsPrincipal (modelPointValuation W) (D + Finsupp.single 0 n) := by
  have hp := (pointIdealProduct_isPrincipal_iff W D).mpr hD
  obtain ⟨f, hf⟩ := (FractionalIdeal.isPrincipal_iff _).mp hp
  have hf0 : f ≠ 0 := by
    have hI0 : FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f ≠ 0 := by
      rw [← hf]
      exact Units.ne_zero _
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mp hI0
  refine ⟨-log (modelPointValuation W 0 f) - D 0, f, hf0, ?_⟩
  intro P
  by_cases hP : P = 0
  · subst P
    simp
  · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hP, add_zero,
      modelPointValuation_of_ne_zero W P hP,
      ← DedekindFractionalValuation.count_spanSingleton _ _ hf0, ← hf]
    exact (count_pointIdealProduct W D P hP).symm

/-- [DkMath.Lib] 任意の二点の加法関係は、無限遠係数を補正した実際の主因子として実現する。 -/
theorem addition_principal_correction (P Q : W.toAffine.Point) :
    ∃ n : ℤ, ValuationDivisor.IsPrincipal (modelPointValuation W)
      (Finsupp.single P 1 + Finsupp.single Q 1 - Finsupp.single (P + Q) 1 + Finsupp.single 0 n) := by
  apply exists_principal_correction
  simp only [map_add, map_sub, pointSum_single, one_zsmul, sub_self]

/-- [DkMath.Lib] アフィンAbel対応の双方向形。Oの係数補正を許した主性と点の総和Oが同値。 -/
theorem exists_principal_correction_iff (D : W.toAffine.Point →₀ ℤ) :
    (∃ n : ℤ, ValuationDivisor.IsPrincipal (modelPointValuation W) (D + Finsupp.single 0 n)) ↔
      pointSum W D = 0 := by
  refine ⟨?_, exists_principal_correction W D⟩
  rintro ⟨n, hn⟩
  have h := pointSum_eq_zero_of_isPrincipal W _ hn
  simpa only [map_add, pointSum_single, zsmul_zero, add_zero] using h

end DkMath.Lib.NumberTheory.WeierstrassDivisorAbel
