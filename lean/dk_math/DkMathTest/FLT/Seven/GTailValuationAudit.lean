/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailValuationAudit

#print "file: DkMathTest.FLT.Seven.GTailValuationAudit"

/-! Conditional interface regression; no positive Fermat solution is supplied. -/

namespace DkMathTest.FLT.Seven.GTailValuationAudit

open DkMath.FLT.Seven

example {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 g = padicValNat 7 a + padicValNat 7 b +
      padicValNat 7 (a + b) + 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2) :=
  padicValNat_focused_gap_balance ha hb hEq hsum hend

#print axioms padicValNat_focused_gap_balance

end DkMathTest.FLT.Seven.GTailValuationAudit
