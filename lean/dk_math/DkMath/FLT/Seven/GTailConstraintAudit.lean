/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailBridge
import DkMath.Lib.Cosmic.GTailSevenArithmetic

#print "file: DkMath.FLT.Seven.GTailConstraintAudit"

/-!
# Focused-gap arithmetic receiver

Height bounds and prime-seven divisibility are transparent conditional
consequences, not new FLT7 obstructions. A smaller positive focused gap does
not construct a smaller counterexample or a descent provider.
-/

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula

/-- Coordinate bounds, with the upper bound obtained from the selected interior. -/
theorem fermat7_focused_bounds {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) : max a b < c ∧ c < a + b := by
  have hbc : b < c := right_lt_of_fermat7Equation ha hEq
  have hswap : Fermat7Equation b a c := by
    simpa only [Fermat7Equation, add_comm] using hEq
  have hac : a < c := right_lt_of_fermat7Equation hb hswap
  have hQ : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  have hinterior : 0 < 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
    positivity
  have hpower : c ^ 7 < (a + b) ^ 7 := by
    rw [add_pow_seven_eq_gap_add_interior]
    change a ^ 7 + b ^ 7 = c ^ 7 at hEq
    omega
  exact ⟨max_lt hac hbc, (Nat.pow_lt_pow_iff_left (by decide : 7 ≠ 0)).mp hpower⟩

/-- Any focused gap satisfying the coordinate relation is smaller than both inputs. -/
theorem focused_gap_lt_coordinates {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) (hsum : c + g = a + b) : g < a ∧ g < b := by
  have hmax := (fermat7_focused_bounds ha hb hEq).1
  have hac : a < c := lt_of_le_of_lt (le_max_left a b) hmax
  have hbc : b < c := lt_of_le_of_lt (le_max_right a b) hmax
  omega

/-- The canonical natural focused gap exists after the upper coordinate bound. -/
theorem exists_positive_focused_gap {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) :
    ∃ g : ℕ, 0 < g ∧ g < a ∧ g < b ∧ c + g = a + b := by
  have hc : c < a + b := (fermat7_focused_bounds ha hb hEq).2
  have hsum : c + (a + b - c) = a + b := Nat.add_sub_of_le hc.le
  have hsmall := focused_gap_lt_coordinates ha hb hEq hsum
  exact ⟨a + b - c, Nat.sub_pos_of_lt hc, hsmall.1, hsmall.2, hsum⟩

/-- The known mod-seven focus condition, recovered through the GTail product. -/
theorem seven_dvd_focused_gap {a b c g : ℕ} (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) : 7 ∣ g := by
  have hp : Nat.Prime 7 := by norm_num
  have hprod : 7 ∣ g * GTail 7 1 g c := by
    rw [gtail_seven_eq_of_fermat7Equation hEq hsum]
    exact ⟨a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2, by ring⟩
  rcases hp.dvd_mul.mp hprod with hgap | htail
  · exact hgap
  · exact (prime_dvd_GN_iff_dvd_gap hp).mp htail

end DkMath.FLT.Seven
