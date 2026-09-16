/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.TwoChannel"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# A two-channel sum/difference coordinate kernel

The kernel records only the real linear change of coordinates
`(u, v) ↦ (u + v, u - v)` and its elementary transport laws.  Domain-specific
arithmetic and analytic interpretations remain in their owner modules.
-/

namespace DkMath.Lib.TwoChannel

noncomputable section

def mass (u v : ℝ) : ℝ := u + v

def balance (u v : ℝ) : ℝ := u - v

def center (u v : ℝ) : ℝ := (u + v) / 2

theorem left_eq_half_mass_add_balance (u v : ℝ) :
    u = (mass u v + balance u v) / 2 := by
  unfold mass balance
  ring

theorem right_eq_half_mass_sub_balance (u v : ℝ) :
    v = (mass u v - balance u v) / 2 := by
  unfold mass balance
  ring

theorem center_eq_half_mass (u v : ℝ) :
    center u v = mass u v / 2 := by
  unfold center mass
  rfl

theorem left_eq_center_add_half_balance (u v : ℝ) :
    u = center u v + balance u v / 2 := by
  unfold center balance
  ring

theorem right_eq_center_sub_half_balance (u v : ℝ) :
    v = center u v - balance u v / 2 := by
  unfold center balance
  ring

theorem balance_eq_zero_iff (u v : ℝ) :
    balance u v = 0 ↔ u = v := by
  unfold balance
  constructor <;> intro h <;> linarith

theorem mass_swap (u v : ℝ) :
    mass v u = mass u v := by
  unfold mass
  ring

theorem center_swap (u v : ℝ) :
    center v u = center u v := by
  unfold center
  ring

theorem balance_swap (u v : ℝ) :
    balance v u = -balance u v := by
  unfold balance
  ring

theorem mass_right_add (u v δ : ℝ) :
    mass u (v + δ) = mass u v + δ := by
  unfold mass
  ring

theorem balance_right_add (u v δ : ℝ) :
    balance u (v + δ) = balance u v - δ := by
  unfold balance
  ring

theorem mass_left_add (u v δ : ℝ) :
    mass (u + δ) v = mass u v + δ := by
  unfold mass
  ring

theorem balance_left_add (u v δ : ℝ) :
    balance (u + δ) v = balance u v + δ := by
  unfold balance
  ring

end

end DkMath.Lib.TwoChannel
