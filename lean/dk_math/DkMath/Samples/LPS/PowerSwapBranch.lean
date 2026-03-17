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

end

end Samples
end DkMath
