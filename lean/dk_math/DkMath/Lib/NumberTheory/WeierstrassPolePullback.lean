/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassFinitePlace
import DkMath.Lib.NumberTheory.EllipticInfinityClassification

#print "file: DkMath.Lib.NumberTheory.WeierstrassPolePullback"

/-!
# 極位数2,3から、無限遠点の正規化された付値を同定する

[DkMath.Lib] 座標環の二元基底p(x)+q(x)yでは、二項の極位数は偶数と奇数になる。
従って最高項の相殺は起こらず、代入後の付値は同じWeierstrassモデルの
ノルム次数による無限遠点付値に一致する。分数表示によって関数体全体へ延長する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassPolePullback
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open WeierstrassCoordinateEvaluation
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (W : WeierstrassCurve k) (x y : F) (hxy : (W.toAffine⁄F).Equation x y)
  (v : Valuation F ℤᵐ⁰)

/-- [DkMath.Lib] 極位数2,3を持つ二座標への代入は、座標環上で無限遠点付値を保存。
二元基底の二項の偶奇が異なることが、相殺を排除する根拠である。 -/
theorem coordinateEval_valuation_infty
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (hx : v x = exp (2 : ℤ)) (hy : v y = exp (3 : ℤ))
    (b : W.toAffine.CoordinateRing) :
    v (coordinateEval W x y hxy b) = EllipticInfinityValuation.valuationInfty W.toAffine
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField b) := by
  by_cases hb : b = 0
  · subst b; simp only [map_zero]
  rw [EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ hb]
  have hC (r : k[X]) (hr : r ≠ 0) :
      v (aeval x r) = exp ((2 * r.natDegree : ℕ) : ℤ) := by
    rw [v.map_aeval_eq_pow_of_one_lt hc (by rw [hx, ← exp_zero, exp_lt_exp]; decide) hr,
      hx, ← exp_nsmul]
    congr 1
    simp [mul_comm]
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq b
  rw [coordinateEval_basis]
  by_cases hq : q = 0
  · subst q
    have hp : p ≠ 0 := by rintro rfl; exact hb (by simp)
    rw [map_zero, zero_mul, add_zero, hC p hp,
      EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_eq_zero]
  · have hB : v (aeval x q * y) = exp ((2 * q.natDegree + 3 : ℕ) : ℤ) := by
      rw [map_mul, hC q hq, hy, ← exp_add]
      congr 1
    rw [EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_ne_zero _ _ _ hq]
    by_cases hp : p = 0
    · subst p
      rw [map_zero, zero_add, hB, natDegree_zero, mul_zero, Nat.zero_max]
    · have hne : v (aeval x p) ≠ v (aeval x q * y) := by
        rw [hC p hp, hB]
        intro he
        have hz := exp_injective he
        omega
      rw [v.map_add_of_distinct_val hne, hC p hp, hB]
      rcases le_total (2 * p.natDegree) (2 * q.natDegree + 3) with h | h
      · rw [max_eq_right h, max_eq_right (exp_le_exp.mpr (by exact_mod_cast h))]
      · rw [max_eq_left h, max_eq_left (exp_le_exp.mpr (by exact_mod_cast h))]

/-- [DkMath.Lib] 同じ極位数の比較を、同じ関数体引き戻しの全ての元へ延長する。
分母は分数体表示で取り、表示の違いは準同型の法則で吸収する。 -/
theorem functionPull_valuation_infty
    (hxt : Transcendental k x) (hyn : y ∉ IntermediateField.adjoin k {x})
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (hx : v x = exp (2 : ℤ)) (hy : v y = exp (3 : ℤ))
    (f : W.toAffine.FunctionField) :
    v (functionPull W x y hxy hxt hyn f) = EllipticInfinityValuation.valuationInfty W.toAffine f := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) f
  rw [map_div₀, map_div₀, map_div₀, functionPull_algebraMap, functionPull_algebraMap,
    coordinateEval_valuation_infty W x y hxy v hc hx hy,
    coordinateEval_valuation_infty W x y hxy v hc hx hy]

end DkMath.Lib.NumberTheory.WeierstrassPolePullback
