/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic

example (y z : ℕ) (h : y ≤ z) : z^3 - y^3 = (z - y) * (z^2 + z * y + y^2) := by
  have h_pow : y^3 ≤ z^3 := Nat.pow_le_pow_left h 3
  zify [h, h_pow]
  ring
