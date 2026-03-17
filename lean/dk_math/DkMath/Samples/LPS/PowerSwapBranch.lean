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

end

end Samples
end DkMath
