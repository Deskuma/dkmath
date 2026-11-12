/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPi

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicBounds"

/-!
# 内在的な内外近似と誤差評価

第一座標 `c_n` は `1-c_n ≤ 2⁻ⁿ` を満たす。これから `c_n → 1` を得る。
外側の候補 `U_n` は面積候補の上限以上であり、内側の候補 `A_n` との間隔は
高々 `8/4^n` である。これらの証明は円周率や三角関数を使わない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel Filter
open scoped Topology

/-- 各段階の core の 1 からの差は非負である。 -/
theorem one_sub_core_nonneg (n : ℕ) : 0 ≤ 1 - (sequence n).core := by
  have := (sequence n).core_le_one
  linarith

/-- 二分後は core の 1 からの差が少なくとも半分に減る。 -/
theorem one_sub_core_succ_le (n : ℕ) :
    1 - (sequence (n+1)).core ≤ (1 - (sequence n).core) / 2 := by
  have hs := core_succ_sq n
  have hc := (sequence (n+1)).core_nonneg
  change 0 ≤ (sequence (n+1)).core at hc
  have hle := (sequence (n+1)).core_le_one
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hle)]

/-- `0 ≤ 1-c_n ≤ (1/2)^n`。角度や三角関数に依存しない誤差評価。 -/
theorem one_sub_core_le (n : ℕ) : 1 - (sequence n).core ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [QuadrantUnitKernel.sequence, initial, core]
  | succ n ih =>
    calc
      1 - (sequence (n+1)).core ≤ (1 - (sequence n).core) / 2 := one_sub_core_succ_le n
      _ ≤ (1 / 2 : ℝ) ^ n / 2 := by linarith
      _ = (1 / 2 : ℝ) ^ (n+1) := by rw [pow_succ]; ring

/-- 第一座標は 1 に収束する。 -/
theorem tendsto_core_one : Tendsto (fun n => (sequence n).core) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : Tendsto (fun n => 1 - (sequence n).core) atTop (𝓝 0) :=
    squeeze_zero one_sub_core_nonneg one_sub_core_le hp
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hz
  simpa using h

/-- 内側の近似は同じ段階の外側の候補以下である。 -/
theorem areaApprox_le_outerApprox (n : ℕ) : areaApprox n ≤ outerApprox n := by
  have hp := core_succ_pos n
  have hc := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+1)
  have hr := areaApprox_eq_core_mul_succ n
  unfold outerApprox
  apply (le_div_iff₀ hp).2
  have hc0 : 0 ≤ (sequence (n+1)).core := le_of_lt hp
  have hsq : (sequence (n+1)).core ^ 2 ≤ 1 := by nlinarith
  have hm := mul_nonneg ha (sub_nonneg.mpr hsq)
  rw [hr]
  nlinarith

/-- 各外側候補は、すべての内側候補の上界である。 -/
theorem areaApprox_le_outerApprox_of_le (n m : ℕ) (h : n ≤ m) :
    areaApprox m ≤ outerApprox n :=
  (areaApprox_le_outerApprox m).trans (outerApprox_antitone h)

/-- 内在的上限は各段階の外側候補以下である。 -/
theorem intrinsicPi_le_outerApprox (n : ℕ) : intrinsicPi ≤ outerApprox n := by
  unfold intrinsicPi
  apply csSup_le (Set.range_nonempty areaApprox)
  rintro _ ⟨m, rfl⟩
  by_cases h : n ≤ m
  · exact areaApprox_le_outerApprox_of_le n m h
  · exact (areaApprox_monotone (Nat.le_of_not_ge h)).trans (areaApprox_le_outerApprox n)

/-- 二分後の第一座標は少なくとも `1/2` であり、商の評価に使える。 -/
theorem one_half_le_core_succ (n : ℕ) : (1 / 2 : ℝ) ≤ (sequence (n+1)).core := by
  have hs := core_succ_sq n
  have hc := (sequence n).core_nonneg
  have hp := core_succ_pos n
  change 0 ≤ (sequence n).core at hc
  nlinarith


/-- 面積候補の上界 `A_(n+1) ≤ 4` から得る beam の幾何級数評価。 -/
theorem beam_succ_le_half_pow (n : ℕ) :
    (sequence (n+1)).beam ≤ (1 / 2 : ℝ) ^ n := by
  have h := areaApprox_le_four (n+1)
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ n * (sequence (n+1)).beam ≤ 1 := by
    simp only [areaApprox, pow_succ] at h
    nlinarith
  have hdiv : (sequence (n+1)).beam ≤ 1 / (2 : ℝ) ^ n := by
    apply (le_div_iff₀ hp).2
    nlinarith
  simpa only [one_div, inv_pow] using hdiv

/--
保存量 `c²+s²=1` による内外誤差の正確な表示。
分母の core は `core_succ_pos` により正である。
-/
theorem outerApprox_sub_areaApprox_eq (n : ℕ) :
    outerApprox n - areaApprox n =
      areaApprox (n+1) * (sequence (n+1)).beam ^ 2 / (sequence (n+1)).core := by
  have hn : (sequence (n+1)).core ≠ 0 := ne_of_gt (core_succ_pos n)
  have hq := (sequence (n+1)).norm
  rw [outerApprox, areaApprox_eq_core_mul_succ n]
  field_simp
  have he : 1 - (sequence (n+1)).core ^ 2 = (sequence (n+1)).beam ^ 2 := by linarith
  rw [he]

/--
π-free の高精度評価 `0 ≤ U_n-A_n ≤ 8(1/4)^n`。
`A_(n+1) ≤ 4`、`c_(n+1) ≥ 1/2` と beam の二乗評価を用いる。
-/
theorem outerApprox_sub_areaApprox_le_quarter_pow (n : ℕ) :
    outerApprox n - areaApprox n ≤ 8 * (1 / 4 : ℝ) ^ n := by
  have hp := core_succ_pos n
  have hc := one_half_le_core_succ n
  have ha := areaApprox_nonneg (n+1)
  have ha4 := areaApprox_le_four (n+1)
  have hb := beam_succ_le_half_pow n
  have hb0 := (sequence (n+1)).beam_nonneg
  change 0 ≤ (sequence (n+1)).beam at hb0
  have ht0 : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  have hs : (sequence (n+1)).beam ^ 2 ≤ (1 / 4 : ℝ) ^ n := by
    have ht : (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = (1 / 4 : ℝ) ^ n := by
      rw [← mul_pow]
      congr 1
      norm_num
    rw [← ht]
    nlinarith
  have hm : areaApprox (n+1) * (sequence (n+1)).beam ^ 2 ≤
      4 * (1 / 4 : ℝ) ^ n := by
    have := mul_nonneg (sub_nonneg.mpr ha4) (sq_nonneg (sequence (n+1)).beam)
    nlinarith
  rw [outerApprox_sub_areaApprox_eq, div_le_iff₀ hp]
  have := mul_nonneg (sub_nonneg.mpr hc) (pow_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) n)
  nlinarith

/-- 内側の候補から内在的定数までの差にも `4⁻ⁿ` 評価が成り立つ。 -/
theorem intrinsicPi_sub_areaApprox_le_quarter_pow (n : ℕ) :
    0 ≤ intrinsicPi - areaApprox n ∧
      intrinsicPi - areaApprox n ≤ 8 * (1 / 4 : ℝ) ^ n := by
  constructor
  · exact sub_nonneg.mpr (areaApprox_le_intrinsicPi n)
  · have h := intrinsicPi_le_outerApprox n
    have he := outerApprox_sub_areaApprox_le_quarter_pow n
    linarith

/-- 内在的定数から外側の候補までの差にも `4⁻ⁿ` 評価が成り立つ。 -/
theorem outerApprox_sub_intrinsicPi_le_quarter_pow (n : ℕ) :
    0 ≤ outerApprox n - intrinsicPi ∧
      outerApprox n - intrinsicPi ≤ 8 * (1 / 4 : ℝ) ^ n := by
  constructor
  · exact sub_nonneg.mpr (intrinsicPi_le_outerApprox n)
  · have h := areaApprox_le_intrinsicPi n
    have he := outerApprox_sub_areaApprox_le_quarter_pow n
    linarith

/-- 内外の差に対する π-free の明示的誤差上界。 -/
theorem outerApprox_sub_areaApprox_le (n : ℕ) :
    outerApprox n - areaApprox n ≤ 8 * (1 / 2 : ℝ) ^ n := by
  have hp := core_succ_pos n
  have hc := one_half_le_core_succ n
  have hle := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+1)
  have ha4 := areaApprox_le_four (n+1)
  have hsq := core_succ_sq n
  have he := one_sub_core_le n
  have he0 := one_sub_core_nonneg n
  have hr := areaApprox_eq_core_mul_succ n
  have hmul : areaApprox (n+1) * (1 - (sequence (n+1)).core ^ 2) ≤
      4 * (1 - (sequence n).core) / 2 := by
    have := mul_nonneg (sub_nonneg.mpr ha4) he0
    nlinarith
  unfold outerApprox
  rw [sub_le_iff_le_add, div_le_iff₀ hp]
  nlinarith

/-- 内側と外側の候補の差は 0 に収束する。 -/
theorem tendsto_outer_sub_area_zero :
    Tendsto (fun n => outerApprox n - areaApprox n) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hp.const_mul 8
  have h' : Tendsto (fun n : ℕ => 8 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by simpa using h
  exact squeeze_zero (fun n => sub_nonneg.mpr (areaApprox_le_outerApprox n))
    outerApprox_sub_areaApprox_le h'

/-- 外側の候補も内在的上限に収束する。 -/
theorem tendsto_outerApprox_intrinsicPi : Tendsto outerApprox atTop (𝓝 intrinsicPi) := by
  have h := tendsto_outer_sub_area_zero.add tendsto_areaApprox_intrinsicPi
  simpa using h

/-- 内在的定数は各段階で内側と外側の候補の間にある。 -/
theorem intrinsicPi_bounds (n : ℕ) : areaApprox n ≤ intrinsicPi ∧ intrinsicPi ≤ outerApprox n :=
  ⟨areaApprox_le_intrinsicPi n, intrinsicPi_le_outerApprox n⟩


/-- 内在的定数と内側の候補の差も、内外の差によって評価される。 -/
theorem intrinsicPi_sub_areaApprox_le (n : ℕ) :
    intrinsicPi - areaApprox n ≤ 8 * (1 / 2 : ℝ) ^ n := by
  have h := intrinsicPi_le_outerApprox n
  have he := outerApprox_sub_areaApprox_le n
  linarith

/-- 外側の候補と内在的定数の差も同じ誤差上界を持つ。 -/
theorem outerApprox_sub_intrinsicPi_le (n : ℕ) :
    outerApprox n - intrinsicPi ≤ 8 * (1 / 2 : ℝ) ^ n := by
  have h := areaApprox_le_intrinsicPi n
  have he := outerApprox_sub_areaApprox_le n
  linarith

end DkMath.CosmicFormula.Rotation.CF2D
