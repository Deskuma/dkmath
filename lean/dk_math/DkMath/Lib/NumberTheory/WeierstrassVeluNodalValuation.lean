/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from blob ab1aee61bdcfbe439dcf9693d5f1417cacc05b6b,
P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean.
Modified: general finite index sets and DkMath normalized coordinates.
-/
import DkMath.Lib.NumberTheory.WeierstrassVeluFormal

#print "file: DkMath.Lib.NumberTheory.WeierstrassVeluNodalValuation"

/-!
# 節点近傍での Vélu 補正の付値

[DkMath.Lib] 非零核点の x 水準が互いに離れているとき、他の水準の補正は小さい。
同じ水準では主項が支配し、補正の付値は 1 以上となる。
曲線の存在や水準の分離をこの解析だけから主張しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVeluNodalValuation
open scoped BigOperators
variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- [DkMath.Lib] 節点からの二つの距離の付値が異なるとき、正規化補正は 1 より小さい。
小さい誤差の条件が二次分母の支配に必要である。 -/
theorem off_level_correction_lt_one (v : Valuation F Γ₀) {β X Xk ε4 : F}
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X ≤ 1) (hXk : v Xk < 1) (hne : v X ≠ v Xk)
    (hsh : v ε4 < v Xk ^ 2) :
    v ((β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4) / (X - Xk) ^ 2) < 1 := by
  have hXk0 : v Xk ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  have hXkpos : (0 : Γ₀) < v Xk := zero_lt_iff.mpr hXk0
  have hXksq : (0 : Γ₀) < v Xk ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hXk0)
  have hM : v (X - Xk) = max (v X) (v Xk) := by
    rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val, Valuation.map_neg]
    rw [Valuation.map_neg]
    exact hne
  rw [map_div₀, map_pow, hM]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hXlt : v X < 1 := hlt.trans hXk
    rw [max_eq_right hlt.le, div_lt_one₀ hXksq]
    have m1 : v (β * Xk * X) < v Xk ^ 2 := by
      rw [map_mul, map_mul, hβ, one_mul, sq]
      exact (mul_lt_mul_iff_right₀ hXkpos).mpr hlt
    have m2 : v (6 * Xk ^ 2 * X) < v Xk ^ 2 := by
      rw [map_mul, map_mul, map_pow, mul_assoc]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
      calc v Xk ^ 2 * v X < v Xk ^ 2 * 1 := (mul_lt_mul_iff_right₀ hXksq).mpr hXlt
        _ = v Xk ^ 2 := mul_one _
    have m3 : v (2 * Xk ^ 3) < v Xk ^ 2 := by
      rw [map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
      exact pow_lt_pow_right_of_lt_one₀ hXkpos hXk (by norm_num)
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_add_lt _ m1 m2) m3) hsh
  · have hXpos : (0 : Γ₀) < v X := lt_trans hXkpos hgt
    have hXsq : (0 : Γ₀) < v X ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 (zero_lt_iff.mp hXpos))
    rw [max_eq_left hgt.le, div_lt_one₀ hXsq]
    have hsq : v Xk ^ 2 < v X ^ 2 := pow_lt_pow_left₀ hgt zero_le two_ne_zero
    have m1 : v (β * Xk * X) < v X ^ 2 := by
      rw [map_mul, map_mul, hβ, one_mul, sq]
      exact (mul_lt_mul_iff_left₀ hXpos).mpr hgt
    have m2 : v (6 * Xk ^ 2 * X) < v X ^ 2 := by
      rw [map_mul, map_mul, map_pow, mul_assoc]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hX) hsq
    have m3 : v (2 * Xk ^ 3) < v X ^ 2 := by
      rw [map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
      calc v Xk ^ 3 < v X ^ 3 := pow_lt_pow_left₀ hgt zero_le three_ne_zero
        _ = v X ^ 2 * v X := by rw [pow_succ]
        _ ≤ v X ^ 2 := mul_le_of_le_one_right' hX
    have m4 : v ε4 < v X ^ 2 := lt_trans hsh hsq
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_add_lt _ m1 m2) m3) m4

/-- [DkMath.Lib] 節点からの距離の付値が等しいとき、分子の支配項は β Xk X である。 -/
theorem same_level_numerator_value (v : Valuation F Γ₀) {β X Xk ε4 : F}
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X < 1) (hX0 : v X ≠ 0) (heq : v Xk = v X)
    (hsh : v ε4 < v X ^ 2) :
    v (β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4) = v X ^ 2 := by
  have hXpos : (0 : Γ₀) < v X := zero_lt_iff.mpr hX0
  have hXsq : (0 : Γ₀) < v X ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hX0)
  have hrw : β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4
      = β * Xk * X + (6 * Xk ^ 2 * X - (2 * Xk ^ 3) - ε4) := by ring
  have m1 : v (β * Xk * X) = v X ^ 2 := by
    rw [map_mul, map_mul, hβ, one_mul, heq, sq]
  have m2 : v (6 * Xk ^ 2 * X) < v X ^ 2 := by
    rw [map_mul, map_mul, map_pow, heq, mul_assoc]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
    calc v X ^ 2 * v X < v X ^ 2 * 1 := (mul_lt_mul_iff_right₀ hXsq).mpr hX
      _ = v X ^ 2 := mul_one _
  have m3 : v (2 * Xk ^ 3) < v X ^ 2 := by
    rw [map_mul, map_pow, heq]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
    exact pow_lt_pow_right_of_lt_one₀ hXpos hX (by norm_num)
  have hR : v (6 * Xk ^ 2 * X - (2 * Xk ^ 3) - ε4) < v (β * Xk * X) := by
    rw [m1]
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ m2 m3) hsh
  rw [hrw, Valuation.map_add_eq_of_lt_left _ hR, m1]

/-- [DkMath.Lib] 等しい水準では、曲線補正の分子の付値は距離の二乗に等しい。
分母は超距離不等式により高々その二乗なので、補正の付値は 1 以上になる。
衝突分母は非零とし、誤差が主項より小さいという仮定を保持する。 -/
theorem same_level_correction_ge_one (v : Valuation F Γ₀) {β X Xk ε4 : F}
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X < 1) (hX0 : v X ≠ 0) (heq : v Xk = v X)
    (hsh : v ε4 < v X ^ 2) (hd : X - Xk ≠ 0) :
    1 ≤ v ((β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4) / (X - Xk) ^ 2) := by
  have hn := same_level_numerator_value v hβ h6 h2 hX hX0 heq hsh
  have hd0 : v (X - Xk) ≠ 0 := fun hz => hd (v.zero_iff.mp hz)
  have hdle : v (X - Xk) ≤ v X := v.map_sub_le le_rfl heq.le
  rw [map_div₀, map_pow, hn, one_le_div₀ (zero_lt_iff.mpr (pow_ne_zero 2 hd0))]
  exact pow_le_pow_left₀ zero_le hdle 2

/-- [DkMath.Lib] 有限個の核水準がすべて入力点の水準と異なれば、補正の総和は小さい。
核点の幾何学的構成や水準分離は、この評価の外部で供給する。 -/
theorem off_level_sum_lt_one {ι : Type*} (v : Valuation F Γ₀) (s : Finset ι)
    (β X ε4 : F) (Xk : ι → F) (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X ≤ 1) (hk : ∀ i ∈ s, v (Xk i) < 1)
    (hne : ∀ i ∈ s, v X ≠ v (Xk i)) (hsh : ∀ i ∈ s, v ε4 < v (Xk i) ^ 2) :
    v (∑ i ∈ s, (β * Xk i * X + 6 * (Xk i) ^ 2 * X - 2 * (Xk i) ^ 3 - ε4) /
      (X - Xk i) ^ 2) < 1 := by
  exact v.map_sum_lt one_ne_zero (fun i hi =>
    off_level_correction_lt_one v hβ h6 h2 hX (hk i hi) (hne i hi) (hsh i hi))

/-- [DkMath.Lib] 入力点が一つの核水準とだけ一致するとき、その補正が他の全補正と
入力点の節点距離を支配する。結果の付値は 1 以上であり、商座標は節点に近くない。 -/
theorem unique_level_sum_ge_one {ι : Type*} (v : Valuation F Γ₀) (s : Finset ι)
    (β X ε4 : F) (Xk : ι → F) (j : ι) (hj : j ∈ s)
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1) (hX : v X < 1) (hX0 : v X ≠ 0)
    (hk : ∀ i ∈ s, v (Xk i) < 1) (heq : v (Xk j) = v X)
    (hne : ∀ i ∈ s, i ≠ j → v X ≠ v (Xk i))
    (hsh : ∀ i ∈ s, v ε4 < v (Xk i) ^ 2) (hd : X - Xk j ≠ 0) :
    1 ≤ v (X + ∑ i ∈ s, (β * Xk i * X + 6 * (Xk i) ^ 2 * X - 2 * (Xk i) ^ 3 - ε4) /
      (X - Xk i) ^ 2) := by
  classical
  let f : ι → F := fun i => (β * Xk i * X + 6 * (Xk i) ^ 2 * X - 2 * (Xk i) ^ 3 - ε4) /
    (X - Xk i) ^ 2
  have hs : v (∑ i ∈ s.erase j, f i) < 1 := by
    apply off_level_sum_lt_one v (s.erase j) β X ε4 Xk hβ h6 h2 hX.le
    · exact fun i hi => hk i (Finset.mem_of_mem_erase hi)
    · exact fun i hi => hne i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    · exact fun i hi => hsh i (Finset.mem_of_mem_erase hi)
  have hrest : v (X + ∑ i ∈ s.erase j, f i) < 1 := v.map_add_lt hX hs
  have hmain : 1 ≤ v (f j) := by
    apply same_level_correction_ge_one v hβ h6 h2 hX hX0 heq _ hd
    simpa only [heq] using hsh j hj
  change 1 ≤ v (X + ∑ i ∈ s, f i)
  rw [← Finset.add_sum_erase _ _ hj]
  have he : X + (f j + ∑ i ∈ s.erase j, f i) = f j + (X + ∑ i ∈ s.erase j, f i) := by ring
  rw [he, Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_le hrest hmain)]
  exact hmain

end DkMath.Lib.NumberTheory.WeierstrassVeluNodalValuation
