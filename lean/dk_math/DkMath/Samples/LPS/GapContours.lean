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

/-! ## GapContours（定義層 + 最小補題） -/

/-- `U = y * log x`。 -/
def gapU (x y : ℝ) : ℝ :=
  y * Real.log x

/-- `V = x * log y`。 -/
def gapV (x y : ℝ) : ℝ :=
  x * Real.log y

/-- `p = (U+V)/2`。 -/
def gapP (x y : ℝ) : ℝ :=
  (gapU x y + gapV x y) / 2

/-- `q = U - V`。 -/
def gapQ (x y : ℝ) : ℝ :=
  gapU x y - gapV x y

/-- `H(x) = log x / x`。 -/
def harmonicCoord (x : ℝ) : ℝ :=
  Real.log x / x

/-- `F(x,y) = x^y - y^x`（`rpow` 版）。 -/
def gapF (x y : ℝ) : ℝ :=
  Real.rpow x y - Real.rpow y x

/-- `gapF` の指数形: `x^y - y^x = exp(U) - exp(V)`。 -/
theorem gapF_eq_expU_sub_expV (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    gapF x y = Real.exp (gapU x y) - Real.exp (gapV x y) := by
  unfold gapF gapU gapV
  simp [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, mul_comm]

/--
`gapQ` は調和座標差の重み付き形
`xy * (H(x) - H(y))` で書ける。
-/
theorem gapQ_eq_xy_mul_Hdiff (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    gapQ x y = x * y * (harmonicCoord x - harmonicCoord y) := by
  unfold gapQ gapU gapV harmonicCoord
  field_simp [hx, hy]

end

end Samples
end DkMath
