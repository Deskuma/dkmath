/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSeven
import DkMath.FLT.Seven.Basic

#print "file: DkMath.FLT.Seven.GTailBridge"

/-!
# Degree-seven GTail bridge

The shell is valid without a Fermat premise. The natural Fermat adapter uses
only addition cancellation; these identities do not establish an obstruction
or a descending map.
-/

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula

/-- Nonvacuous seven-power shell from an additive coordinate relation alone. -/
theorem gtail_seven_shell {R : Type*} [CommSemiring R] (a b c g : R)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c + c ^ 7 = (a ^ 7 + b ^ 7) +
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  calc
    g * GTail 7 1 g c + c ^ 7 = (g + c) ^ 7 :=
      (add_pow_eq_mul_GTail_one_add_gap 7 g c).symm
    _ = (a + b) ^ 7 := by rw [add_comm g c, ← hsum]
    _ = (a ^ 7 + b ^ 7) +
        7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
      simpa only [add_comm b a, add_comm (b ^ 7) (a ^ 7)] using
        add_pow_seven_eq_gap_add_interior a b

/-- Ring-valued deviation from the Fermat equation, derived from the shell. -/
theorem gtail_seven_defect {R : Type*} [CommRing R] (a b c g : R)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 +
        (a ^ 7 + b ^ 7 - c ^ 7) := by
  have hshell := gtail_seven_shell a b c g hsum
  linear_combination hshell

/-- Conditional natural bridge: rewrite the equation and cancel the same endpoint. -/
theorem gtail_seven_eq_of_fermat7Equation {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  have hshell := gtail_seven_shell a b c g hsum
  change a ^ 7 + b ^ 7 = c ^ 7 at hEq
  rw [hEq, add_comm (c ^ 7)] at hshell
  exact Nat.add_right_cancel hshell

/-- Candidate-packet adapter; only its equation field is consumed. -/
theorem gtail_seven_eq_of_counterexamplePack {a b c g : ℕ}
    (h : CounterexamplePack a b c) (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  gtail_seven_eq_of_fermat7Equation h.hEq hsum

end DkMath.FLT.Seven
