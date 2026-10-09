/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailBridge
import DkMath.Lib.NumberTheory.GTailSevenNormReadout

#print "file: DkMath.FLT.Seven.GTailNormReadoutAudit"

/-!
# Conditional integer norm readout

Cast the exact natural focused product, preserving its natural GTail value.
Equality of norm values does not supply an algebraic factorization or descent.
-/

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

/-- The focused natural product has a typed quadratic-ring norm-square readout in integers. -/
theorem focused_gtail_eq_norm_square {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    (g : ℤ) * ((DkMath.CosmicFormula.GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) := by
  have hcast := congrArg (fun n : ℕ => (n : ℤ))
    (gtail_seven_eq_of_fermat7Equation hEq hsum)
  rw [norm_gtailSevenNormCoord_sq]
  push_cast at hcast ⊢
  exact hcast

end DkMath.FLT.Seven
