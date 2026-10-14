/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge

#print "file: DkMath.FLT.Seven.GTailGlobalBalanceFirewall"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic

/-- Under additive focus, exact scalar balance is equivalent to the original equation. -/
theorem fermat7Equation_iff_focused_scalar_balance {a b c g : ℕ}
    (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  refine ⟨fun h => gtail_seven_eq_of_fermat7Equation h hfocus, ?_⟩
  intro hbalance
  have hshell := gtail_seven_shell a b c g hfocus
  rw [hbalance] at hshell
  change a ^ 7 + b ^ 7 = c ^ 7
  omega

/-- Integer norm balance retains the exact equation, not an integral carrier transport. -/
theorem fermat7Equation_iff_focused_norm_balance {a b c g : ℕ}
    (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) := by
  refine ⟨fun h => focused_gtail_eq_norm_square h hfocus, ?_⟩
  intro hbalance
  rw [norm_gtailSevenNormCoord_sq] at hbalance
  apply (fermat7Equation_iff_focused_scalar_balance hfocus).mpr
  exact_mod_cast hbalance

end DkMath.FLT.Seven
