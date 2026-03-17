/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- LPS module: Lander, Parkin, and Selfridge conjecture research

import Mathlib

namespace DkMath
namespace Samples

noncomputable section

/-! ## PowerSwap の実数 branch（定義層） -/

/-- PowerSwap 実数 branch のパラメータ領域。 -/
def PowerSwapBranchDomain (t : ℝ) : Prop :=
  0 < t ∧ t ≠ 1

/-- `x(t) = t^(1/(t-1))`。 -/
def powerSwapBranchX (t : ℝ) : ℝ :=
  Real.rpow t (1 / (t - 1))

/-- `y(t) = t^(t/(t-1))`。 -/
def powerSwapBranchY (t : ℝ) : ℝ :=
  Real.rpow t (t / (t - 1))

/-- branch 座標の基礎ペア。 -/
def powerSwapBranchPair (t : ℝ) : ℝ × ℝ :=
  (powerSwapBranchX t, powerSwapBranchY t)

/-- `x(t)` の指数表示: `x(t) = exp(log t / (t-1))`（`t > 0`）。 -/
theorem powerSwap_branchX_eq_exp_log_div_sub (t : ℝ) (ht : 0 < t) :
    powerSwapBranchX t = Real.exp (Real.log t / (t - 1)) := by
  unfold powerSwapBranchX
  simp [Real.rpow_def_of_pos ht, div_eq_mul_inv, mul_comm]

/-- `y(t)` の指数表示: `y(t) = exp((t*log t)/(t-1))`（`t > 0`）。 -/
theorem powerSwap_branchY_eq_exp_mul_log_div_sub (t : ℝ) (ht : 0 < t) :
    powerSwapBranchY t = Real.exp ((t * Real.log t) / (t - 1)) := by
  unfold powerSwapBranchY
  simp [Real.rpow_def_of_pos ht, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/--
`log t / (t-1) → 1` が示せれば、`x(t)` は `e` に収束する。
`limit_to_e` 本体の前段補題。
-/
theorem powerSwap_branchX_tendsto_e_of_log_div_sub_tendsto_one
    (hpos : ∀ᶠ t in nhdsWithin (1 : ℝ) ({1}ᶜ), 0 < t)
    (hlog : Filter.Tendsto (fun t : ℝ => Real.log t / (t - 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds 1)) :
    Filter.Tendsto powerSwapBranchX (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds (Real.exp 1)) := by
  refine Filter.Tendsto.congr' ?_ ((Real.continuous_exp.continuousAt).tendsto.comp hlog)
  filter_upwards [hpos] with t ht
  exact (powerSwap_branchX_eq_exp_log_div_sub t ht).symm

/--
`(t*log t)/(t-1) → 1` が示せれば、`y(t)` は `e` に収束する。
`limit_to_e` 本体の前段補題。
-/
theorem powerSwap_branchY_tendsto_e_of_mul_log_div_sub_tendsto_one
    (hpos : ∀ᶠ t in nhdsWithin (1 : ℝ) ({1}ᶜ), 0 < t)
    (hlog : Filter.Tendsto (fun t : ℝ => (t * Real.log t) / (t - 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds 1)) :
    Filter.Tendsto powerSwapBranchY (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds (Real.exp 1)) := by
  refine Filter.Tendsto.congr' ?_ ((Real.continuous_exp.continuousAt).tendsto.comp hlog)
  filter_upwards [hpos] with t ht
  exact (powerSwap_branchY_eq_exp_mul_log_div_sub t ht).symm

/--
`limit_to_e` の核: 2 つの指数極限が示せれば branch pair は `(e,e)` へ収束する。
-/
theorem powerSwap_branch_limit_to_e_of_core_limits
    (hpos : ∀ᶠ t in nhdsWithin (1 : ℝ) ({1}ᶜ), 0 < t)
    (hlogX : Filter.Tendsto (fun t : ℝ => Real.log t / (t - 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds 1))
    (hlogY : Filter.Tendsto (fun t : ℝ => (t * Real.log t) / (t - 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ)) (nhds 1)) :
    Filter.Tendsto powerSwapBranchPair (nhdsWithin (1 : ℝ) ({1}ᶜ))
      ((nhds (Real.exp 1)) ×ˢ (nhds (Real.exp 1))) := by
  exact (powerSwap_branchX_tendsto_e_of_log_div_sub_tendsto_one hpos hlogX).prodMk
    (powerSwap_branchY_tendsto_e_of_mul_log_div_sub_tendsto_one hpos hlogY)

/-- branch 上で `y(t) = t * x(t)`。 -/
theorem powerSwap_branch_y_eq_t_mul_x (t : ℝ)
    (hdom : PowerSwapBranchDomain t) :
    powerSwapBranchY t = t * powerSwapBranchX t := by
  rcases hdom with ⟨ht, ht_ne_one⟩
  unfold powerSwapBranchY powerSwapBranchX
  have ht1 : (t - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr ht_ne_one
  have hexp : t / (t - 1) = (1 / (t - 1 : ℝ)) + 1 := by
    calc
      t / (t - 1) = ((t - 1) + 1) / (t - 1) := by ring
      _ = (t - 1) / (t - 1) + 1 / (t - 1) := by rw [add_div]
      _ = 1 + 1 / (t - 1) := by simp [ht1]
      _ = (1 / (t - 1 : ℝ)) + 1 := by ring
  calc
    Real.rpow t (t / (t - 1))
        = Real.rpow t ((1 / (t - 1 : ℝ)) + 1) := by rw [hexp]
    _ = Real.rpow t (1 / (t - 1 : ℝ)) * Real.rpow t 1 := by
          simpa [add_comm] using
            (Real.rpow_add (x := t) (y := (1 / (t - 1 : ℝ))) (z := (1 : ℝ)) ht)
    _ = t * Real.rpow t (1 / (t - 1 : ℝ)) := by simp [mul_comm]
    _ = t * powerSwapBranchX t := by rfl

/--
一般形（前提付き）:
`t > 0`, `t ≠ 1` なら branch で `x(t)^y(t) = y(t)^x(t)`。
-/
theorem powerSwap_branch_correct (t : ℝ)
    (hdom : PowerSwapBranchDomain t) :
    Real.rpow (powerSwapBranchX t) (powerSwapBranchY t) =
      Real.rpow (powerSwapBranchY t) (powerSwapBranchX t) := by
  rcases hdom with ⟨ht, ht_ne_one⟩
  have hx_pos : 0 < powerSwapBranchX t := by
    unfold powerSwapBranchX
    exact Real.rpow_pos_of_pos ht _
  have hx_nonneg : 0 ≤ powerSwapBranchX t := le_of_lt hx_pos
  have hxt : Real.rpow (powerSwapBranchX t) t = powerSwapBranchY t := by
    unfold powerSwapBranchX powerSwapBranchY
    calc
      Real.rpow (Real.rpow t (1 / (t - 1 : ℝ))) t
        = Real.rpow t ((1 / (t - 1 : ℝ)) * t) := by
              simpa [mul_comm] using
                (Real.rpow_mul (le_of_lt ht) (1 / (t - 1 : ℝ)) t).symm
      _ = Real.rpow t (t / (t - 1)) := by
        simp [div_eq_mul_inv, mul_comm]
  have hyx : powerSwapBranchY t = t * powerSwapBranchX t :=
    powerSwap_branch_y_eq_t_mul_x t ⟨ht, ht_ne_one⟩
  calc
    Real.rpow (powerSwapBranchX t) (powerSwapBranchY t)
        = Real.rpow (powerSwapBranchX t) (t * powerSwapBranchX t) := by rw [hyx]
    _ = Real.rpow (Real.rpow (powerSwapBranchX t) t) (powerSwapBranchX t) := by
          simpa [mul_comm] using
            (Real.rpow_mul hx_nonneg t (powerSwapBranchX t))
    _ = Real.rpow (powerSwapBranchY t) (powerSwapBranchX t) := by rw [hxt]

/-- branch の整数格子点: `t = 2` で `(x,y) = (2,4)`。 -/
theorem powerSwap_branch_at_two :
    powerSwapBranchX 2 = 2 ∧ powerSwapBranchY 2 = 4 := by
  constructor
  · unfold powerSwapBranchX
    norm_num
  · unfold powerSwapBranchY
    norm_num

/-- branch の整数格子点: `t = 1/2` で `(x,y) = (4,2)`。 -/
theorem powerSwap_branch_at_half :
    powerSwapBranchX (1 / 2 : ℝ) = 4 ∧ powerSwapBranchY (1 / 2 : ℝ) = 2 := by
  constructor
  · unfold powerSwapBranchX
    norm_num
  · unfold powerSwapBranchY
    norm_num

/-- branch の実数標本: `t = 3` で `(x,y) = (3^(1/2), 3^(3/2))`。 -/
theorem powerSwap_branch_at_three :
    powerSwapBranchX 3 = Real.rpow 3 (1 / 2 : ℝ) ∧
    powerSwapBranchY 3 = Real.rpow 3 (3 / 2 : ℝ) := by
  constructor
  · unfold powerSwapBranchX
    norm_num
  · unfold powerSwapBranchY
    norm_num

/-- 段階補題: `t = 3` では `y(3) = 3 * x(3)`。 -/
theorem powerSwap_branch_at_three_y_eq_three_mul_x :
    powerSwapBranchY 3 = 3 * powerSwapBranchX 3 := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  rcases powerSwap_branch_at_three with ⟨hx, hy⟩
  calc
    powerSwapBranchY 3 = Real.rpow 3 (3 / 2 : ℝ) := hy
    _ = Real.rpow 3 ((1 / 2 : ℝ) + 1) := by ring_nf
    _ = Real.rpow 3 (1 / 2 : ℝ) * Real.rpow 3 1 := by
        simpa using
        (Real.rpow_add (x := (3 : ℝ)) (y := (1 / 2 : ℝ)) (z := (1 : ℝ))
            h3pos)
    _ = powerSwapBranchX 3 * 3 := by simp [hx, Real.rpow_one]
    _ = 3 * powerSwapBranchX 3 := by ring

/-- 段階補題: `t = 2` では branch 上で `x^y = y^x` が成立。 -/
theorem powerSwap_branch_correct_at_two :
    Real.rpow (powerSwapBranchX 2) (powerSwapBranchY 2) =
      Real.rpow (powerSwapBranchY 2) (powerSwapBranchX 2) := by
  rcases powerSwap_branch_at_two with ⟨hx, hy⟩
  rw [hx, hy]
  norm_num

/-- 段階補題: `t = 1/2` でも branch 上で `x^y = y^x` が成立。 -/
theorem powerSwap_branch_correct_at_half :
    Real.rpow (powerSwapBranchX (1 / 2 : ℝ)) (powerSwapBranchY (1 / 2 : ℝ)) =
      Real.rpow (powerSwapBranchY (1 / 2 : ℝ)) (powerSwapBranchX (1 / 2 : ℝ)) := by
  rcases powerSwap_branch_at_half with ⟨hx, hy⟩
  rw [hx, hy]
  norm_num

/-- 段階補題: `t = 3` でも branch 上で `x^y = y^x` が成立。 -/
theorem powerSwap_branch_correct_at_three :
    Real.rpow (powerSwapBranchX 3) (powerSwapBranchY 3) =
      Real.rpow (powerSwapBranchY 3) (powerSwapBranchX 3) := by
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  rcases powerSwap_branch_at_three with ⟨hx, hy⟩
  have hyx : Real.rpow 3 (3 / 2 : ℝ) = 3 * Real.rpow 3 (1 / 2 : ℝ) := by
    calc
      Real.rpow 3 (3 / 2 : ℝ) = powerSwapBranchY 3 := by simp [hy]
      _ = 3 * powerSwapBranchX 3 := powerSwap_branch_at_three_y_eq_three_mul_x
      _ = 3 * Real.rpow 3 (1 / 2 : ℝ) := by simp [hx]
  calc
    Real.rpow (powerSwapBranchX 3) (powerSwapBranchY 3)
        = Real.rpow (Real.rpow 3 (1 / 2 : ℝ)) (Real.rpow 3 (3 / 2 : ℝ)) := by
          simp [hx, hy]
    _ = Real.rpow 3 ((1 / 2 : ℝ) * Real.rpow 3 (3 / 2 : ℝ)) := by
          simpa [mul_comm] using
            (Real.rpow_mul h3nonneg (1 / 2 : ℝ) (Real.rpow 3 (3 / 2 : ℝ))).symm
    _ = Real.rpow 3 ((3 / 2 : ℝ) * Real.rpow 3 (1 / 2 : ℝ)) := by
          rw [hyx]
          ring_nf
    _ = Real.rpow 3 ((3 / 2 : ℝ) * Real.rpow 3 (1 / 2 : ℝ)) := by rfl
    _ = Real.rpow (Real.rpow 3 (3 / 2 : ℝ)) (Real.rpow 3 (1 / 2 : ℝ)) := by
          simpa [mul_comm] using
            (Real.rpow_mul h3nonneg (3 / 2 : ℝ) (Real.rpow 3 (1 / 2 : ℝ)))
    _ = Real.rpow (powerSwapBranchY 3) (powerSwapBranchX 3) := by
          simp [hx, hy]

/--
有限標本パック: `t = 2, 1/2, 3` の 3 点で branch 平衡
`x(t)^y(t) = y(t)^x(t)` が成立する。
-/
theorem powerSwap_branch_correct_finite_samples :
    Real.rpow (powerSwapBranchX 2) (powerSwapBranchY 2)
      = Real.rpow (powerSwapBranchY 2) (powerSwapBranchX 2)
    ∧ Real.rpow (powerSwapBranchX (1 / 2 : ℝ)) (powerSwapBranchY (1 / 2 : ℝ))
      = Real.rpow (powerSwapBranchY (1 / 2 : ℝ)) (powerSwapBranchX (1 / 2 : ℝ))
    ∧ Real.rpow (powerSwapBranchX 3) (powerSwapBranchY 3)
      = Real.rpow (powerSwapBranchY 3) (powerSwapBranchX 3) := by
  exact ⟨powerSwap_branch_correct_at_two,
    powerSwap_branch_correct_at_half,
    powerSwap_branch_correct_at_three⟩

end

end Samples
end DkMath
