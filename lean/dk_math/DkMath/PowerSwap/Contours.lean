/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- PowerSwap module: Geometric contours and local analysis near (e,e)

import Mathlib

namespace DkMath
namespace PowerSwap

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
soft hyperbolic form:
`F = 2 * exp(p) * sinh(q/2)`.
-/
theorem gapF_eq_soft_hyperbolic_form (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    gapF x y = 2 * Real.exp (gapP x y) * Real.sinh (gapQ x y / 2) := by
  set U : ℝ := gapU x y
  set V : ℝ := gapV x y
  set p : ℝ := (U + V) / 2
  set q : ℝ := U - V
  have hU : U = p + q / 2 := by
    simp [p, q]
    ring_nf
  have hV : V = p - q / 2 := by
    simp [p, q]
    ring_nf
  calc
    gapF x y = Real.exp U - Real.exp V := by
      simp [U, V, gapF_eq_expU_sub_expV, hx, hy]
    _ = Real.exp (p + q / 2) - Real.exp (p - q / 2) := by rw [hU, hV]
    _ = Real.exp p * Real.exp (q / 2)
      - Real.exp p * Real.exp (-(q / 2)) := by
          have hpm : p - q / 2 = p + (-(q / 2)) := by ring
          rw [hpm, sub_eq_add_neg, Real.exp_add, Real.exp_add]
          ring_nf
    _ = Real.exp p * (Real.exp (q / 2) - Real.exp (-(q / 2))) := by
          ring
    _ = 2 * Real.exp p * Real.sinh (q / 2) := by
          rw [Real.sinh_eq]
          ring
    _ = 2 * Real.exp (gapP x y) * Real.sinh (gapQ x y / 2) := by
      simp [U, V, p, q, gapP, gapQ]

/--
`gapQ` は調和座標差の重み付き形
`xy * (H(x) - H(y))` で書ける。
-/
theorem gapQ_eq_xy_mul_Hdiff (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    gapQ x y = x * y * (harmonicCoord x - harmonicCoord y) := by
  unfold gapQ gapU gapV harmonicCoord
  field_simp [hx, hy]

/-! ## `(e,e)` 中心の最小固定 -/

/-- 中心 `(e,e)` では差座標 `q` は 0。 -/
theorem gapQ_at_e_e :
    gapQ (Real.exp 1) (Real.exp 1) = 0 := by
  unfold gapQ gapU gapV
  simp [mul_comm]

/-- 中心 `(e,e)` では平均座標 `p` は `e`。 -/
theorem gapP_at_e_e :
    gapP (Real.exp 1) (Real.exp 1) = Real.exp 1 := by
  unfold gapP gapU gapV
  simp [mul_comm]

/-- 中心 `(e,e)` では `F(e,e)=0`。 -/
theorem gapF_at_e_e :
    gapF (Real.exp 1) (Real.exp 1) = 0 := by
  have hpos : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
  calc
    gapF (Real.exp 1) (Real.exp 1)
        = 2 * Real.exp (gapP (Real.exp 1) (Real.exp 1))
            * Real.sinh (gapQ (Real.exp 1) (Real.exp 1) / 2) :=
          gapF_eq_soft_hyperbolic_form (Real.exp 1) (Real.exp 1) hpos hpos
    _ = 0 := by simp [gapQ_at_e_e]

/-! ## `(e,e)` 近傍の局所二次モデル（最小固定） -/

/-- `(e,e)` 近傍の局所座標 `x = e+u`。 -/
def localX (u : ℝ) : ℝ := Real.exp 1 + u

/-- `(e,e)` 近傍の局所座標 `y = e+v`。 -/
def localY (v : ℝ) : ℝ := Real.exp 1 + v

/-- 局所二次主部モデル（候補）: `v^2 - u^2`。 -/
def gapQuadraticModel (u v : ℝ) : ℝ := v ^ 2 - u ^ 2

/-- 二次モデルは反対称（引数交換で符号反転）。 -/
theorem gapQuadraticModel_swap_neg (u v : ℝ) :
    gapQuadraticModel v u = -gapQuadraticModel u v := by
  unfold gapQuadraticModel
  ring

/-- 対角上では二次モデルは 0。 -/
theorem gapQuadraticModel_diag_zero (u : ℝ) :
    gapQuadraticModel u u = 0 := by
  unfold gapQuadraticModel
  ring

/-- 局所対角 `u=v`（かつ正値域）では `F(e+u,e+u)=0`。 -/
theorem gapF_local_diag_zero (u : ℝ) :
    gapF (localX u) (localY u) = 0 := by
  unfold gapF localX localY
  ring_nf

end

end PowerSwap
end DkMath
