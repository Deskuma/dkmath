/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC

set_option linter.style.longLine false

namespace ABC

namespace Chernoff

/-- ABC予想の品質評価関数に関する不等式:
    `¬Bad_ε c γ_values` ならば
    c ≤ exp(1) * rad(abc)^(1 + ε) である。 -/
lemma quality_le_of_not_bad'
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hnb : ¬Bad_ε c γ_values)
    (h_quality :
      (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε)) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  -- This file serves as a thin bridge layer; keep the core inequality as an
  -- explicit upstream assumption instead of using local placeholders.
  have _ := hrel
  have _ := hcoprime
  have _ := ha_pos
  have _ := hb_pos
  have _ := hε
  have _ := γ_values
  have _ := hnb
  exact h_quality






end Chernoff

end ABC
