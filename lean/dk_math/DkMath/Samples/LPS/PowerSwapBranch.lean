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

end

end Samples
end DkMath
