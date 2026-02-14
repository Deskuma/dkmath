/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
/-- Cubic difference formula:
$$
\Large
z^3 - y^3 = (z - y)(z^2 + zy + y^2)\\[16pt]
\normalsize
$$
z: Big := Universe
y: Gap := Unit
-/
def x3sub (y z : ℕ) : ℕ := (z - y) * (z ^ 2 + z * y + y ^ 2)
/--
Cubic power formula:
$$
\Large
x^3 = x \cdot x \cdot x\\[16pt]
\normalsize
$$
x: Body := Geometric Value = (Big - Unit)
-/
def x3pow (x : ℕ) : ℕ := x ^ 3

#eval x3sub 1 3  -- 26
#eval x3pow 3    -- 27

#eval x3sub 1 5  -- 124
#eval x3pow 5    -- 125

#eval x3sub 1 7  -- 342
#eval x3pow 7    -- 343

#eval x3sub 1 9  -- 728
#eval x3pow 9    -- 729

#eval x3sub 1 2  -- 7
#eval x3pow 2    -- 8

#eval x3sub 2 3  -- 19
#eval x3pow 3    -- 27

#eval x3sub 4 5  -- 61
#eval x3pow 4    -- 64

#eval x3sub 5 6  -- 91
#eval x3pow 5    -- 125

example {x} (y z : ℕ) : x ^ 3 = (z - y) * (z ^ 2 + z * y + y ^ 2) + 1 := by
  refine (Nat.Prime.pow_eq_iff ?_).mpr ?_
  /-
  case refine_1
  x y z : ℕ
  ⊢ Nat.Prime ((z - y) * (z ^ 2 + z * y + y ^ 2))

  case refine_2
  x y z : ℕ
  ⊢ x = (z - y) * (z ^ 2 + z * y + y ^ 2) ∧ 3 = 1
  -/
  · sorry
  · sorry

example (y z : ℕ) (h : y ≤ z) : z^3 - y^3 = (z - y) * (z^2 + z * y + y^2) := by
  have h_pow : y^3 ≤ z^3 := Nat.pow_le_pow_left h 3
  zify [h, h_pow]
  ring
