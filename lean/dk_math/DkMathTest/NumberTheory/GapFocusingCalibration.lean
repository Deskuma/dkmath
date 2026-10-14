/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.Focus
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

#print "file: DkMathTest.NumberTheory.GapFocusingCalibration"

open DkMath.NumberTheory.GapFocusing DkMath.CosmicFormula Polynomial

/-- Numerical divisibility does not imply vanishing focus defect. -/
example : (2 : ℤ) ∣ (2 + 1) ^ 2 - 5 ^ 2 ∧ (1 : ℤ) ^ 2 ≠ 5 ^ 2 := by
  norm_num

/-- Equality of anchor powers need not determine the anchor. -/
example : (X : ℤ[X]) ∣ (X + C 1) ^ 2 - (C (-1)) ^ 2 := by
  rw [X_dvd_unfocused_iff]
  norm_num

/-- The defect changes under translation of both anchors. -/
example : focusDefect 2 (1 : ℤ) 0 ≠ focusDefect 2 (1 + 1 : ℤ) (0 + 1) := by
  norm_num [focusDefect]

/-- A characteristic-zero unit anchor has only one gap factor. -/
example : ¬ (X : ℤ[X]) ^ 2 ∣ (X + C 1) ^ 3 - (C 1) ^ 3 := by
  rw [X_sq_dvd_focused_iff]
  norm_num

/-- Characteristic can add gap multiplicity even at a unit anchor. -/
example : (X : (ZMod 3)[X]) ^ 2 ∣ (X + C 1) ^ 3 - (C 1) ^ 3 := by
  rw [X_sq_dvd_focused_iff]
  decide

/-- At characteristic three, prime degree alone does not ensure irreducibility. -/
example : GTail 3 1 (X : (ZMod 3)[X]) (C 1) = X ^ 2 := by
  have hthree : (3 : (ZMod 3)[X]) = 0 := by
    change C (3 : ZMod 3) = 0
    rw [show (3 : ZMod 3) = 0 by decide, C_0]
  norm_num [GTail, Finset.sum_range_succ]
  simp [hthree]

/-- Zero gap retains the first coefficient; numerical cancellation cannot recover it. -/
example : GTail 3 1 (0 : ℤ) 2 = 12 := by
  rw [GN_zero_eval]
  norm_num
