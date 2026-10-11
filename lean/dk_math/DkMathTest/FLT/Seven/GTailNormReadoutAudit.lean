/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailNormReadoutAudit

#print "file: DkMathTest.FLT.Seven.GTailNormReadoutAudit"

/-! Conditional exact norm interface and a satisfiable zero-boundary equation. -/

namespace DkMathTest.FLT.Seven.GTailNormReadoutAudit

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory
open DkMath.CosmicFormula DkMath.FLT.Seven

example {a b c g : ℕ} (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) :=
  focused_gtail_eq_norm_square hEq hsum

-- This boundary equation is satisfiable; it is not a positive Fermat candidate.
example : (0 : ℤ) * ((GTail 7 1 0 3 : ℕ) : ℤ) =
    7 * (0 : ℤ) * 3 * 3 * norm ((gtailSevenNormCoord 0 3 : TraceOneInt (-1)) ^ 2) :=
  focused_gtail_eq_norm_square (a := 0) (b := 3) (c := 3) (g := 0)
    (by norm_num [Fermat7Equation]) (by decide)

#print axioms focused_gtail_eq_norm_square

end DkMathTest.FLT.Seven.GTailNormReadoutAudit
