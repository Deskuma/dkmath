/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailConstraintAudit
import DkMath.Lib.Cosmic.GTailSevenValuation

#print "file: DkMath.FLT.Seven.GTailValuationAudit"

/-!
# Conditional focused-gap valuation conservation

This is a necessary product identity with an explicit endpoint unit. It
constructs no counterexample, contradiction, or descending packet.
-/

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula

/-- Cancel exactly one seven-adic layer on both sides of the focused product. -/
theorem padicValNat_focused_gap_balance {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 g = padicValNat 7 a + padicValNat 7 b +
      padicValNat 7 (a + b) + 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hheight := (fermat7_focused_bounds ha hb hEq).2
  have hg : g ≠ 0 := by omega
  have hgap := seven_dvd_focused_gap hEq hsum
  have hQ : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  have h7ab : 7 * a * b ≠ 0 := by positivity
  have hsum0 : a + b ≠ 0 := by positivity
  have hprefix : 7 * a * b * (a + b) ≠ 0 := by positivity
  have hQsq : (a ^ 2 + a * b + b ^ 2) ^ 2 ≠ 0 := by positivity
  have hval := congrArg (padicValNat 7)
    (gtail_seven_eq_of_fermat7Equation hEq hsum)
  rw [padicValNat_gap_mul_gtail_seven hg hgap hend,
    padicValNat.mul hprefix hQsq, padicValNat.mul h7ab hsum0,
    padicValNat.mul (by positivity : 7 * a ≠ 0) (Nat.ne_of_gt hb),
    padicValNat.mul (by norm_num : 7 ≠ 0) (Nat.ne_of_gt ha),
    padicValNat.pow, padicValNat_self] at hval
  omega

end DkMath.FLT.Seven
