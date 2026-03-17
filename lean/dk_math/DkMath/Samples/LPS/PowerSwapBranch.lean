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
