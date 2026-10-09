/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailValuationAudit
import DkMath.Lib.NumberTheory.SevenUnitAllocation

#print "file: DkMath.FLT.Seven.GTailSevenUnitAudit"

/-!
# Conditional seven-unit focused branch

Exact Fermat equations, not congruence-only compatibility, drive the unit
transfer and valuation balance. These necessary conditions give no descent.
-/

namespace DkMath.FLT.Seven

/-- The exact equation transfers the endpoint unit to the coordinate sum. -/
theorem not_seven_dvd_sum_of_focused_equation {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) (hc : ¬ 7 ∣ c) :
    ¬ 7 ∣ a + b := by
  have hg := seven_dvd_focused_gap hEq hsum
  intro hsumdvd
  have htotal : 7 ∣ c + g := hsum ▸ hsumdvd
  exact hc ((Nat.dvd_add_left hg).mp htotal)

/-- In the exact unit branch only the squared quadratic contributes valuation. -/
theorem padicValNat_focused_gap_unit_balance {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    padicValNat 7 g = 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2) := by
  have hbalance := padicValNat_focused_gap_balance ha hb hEq hsum huc
  rw [padicValNat.eq_zero_of_not_dvd hua, padicValNat.eq_zero_of_not_dvd hub,
    padicValNat.eq_zero_of_not_dvd (not_seven_dvd_sum_of_focused_equation hEq hsum huc)]
    at hbalance
  simpa using hbalance

/-- The unit branch forces the quadratic onto its seven-divisibility channel. -/
theorem seven_dvd_quadratic_of_focused_units {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    7 ∣ a ^ 2 + a * b + b ^ 2 := by
  have hheight := (fermat7_focused_bounds ha hb hEq).2
  have hg : g ≠ 0 := by omega
  have hge := (DkMath.Lib.NumberTheory.Vp_ge_one_iff
    (by decide : Nat.Prime 7) hg).mpr (seven_dvd_focused_gap hEq hsum)
  have hv := padicValNat_focused_gap_unit_balance ha hb hEq hsum hua hub huc
  have hQ : a ^ 2 + a * b + b ^ 2 ≠ 0 := by positivity
  apply (DkMath.Lib.NumberTheory.Vp_ge_one_iff (by decide : Nat.Prime 7) hQ).mp
  omega

/-- The positive even carrier valuation in the exact unit branch is at least two. -/
theorem fortyNine_dvd_focused_gap_of_units {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    49 ∣ g := by
  have hheight := (fermat7_focused_bounds ha hb hEq).2
  have hg : g ≠ 0 := by omega
  exact DkMath.Lib.NumberTheory.fortyNine_dvd_of_seven_dvd_of_valuation_double hg
    (seven_dvd_focused_gap hEq hsum)
    (padicValNat_focused_gap_unit_balance ha hb hEq hsum hua hub huc)

end DkMath.FLT.Seven
