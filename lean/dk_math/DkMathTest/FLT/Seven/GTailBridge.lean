/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailBridge

#print "file: DkMathTest.FLT.Seven.GTailBridge"

/-! Regression checks for the nonvacuous shell and its algebraic adapters. -/

namespace DkMathTest.FLT.Seven.GTailBridge

open DkMath.CosmicFormula DkMath.FLT.Seven

example {R : Type*} [CommSemiring R] (a b c g : R) (h : a + b = c + g) :
    g * GTail 7 1 g c + c ^ 7 = (a ^ 7 + b ^ 7) +
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  gtail_seven_shell a b c g h

-- Satisfiable coordinates; no Fermat premise.
example : (1 : ℕ) * GTail 7 1 1 4 + 4 ^ 7 =
    (2 ^ 7 + 3 ^ 7) + 7 * 2 * 3 * (2 + 3) * (2 ^ 2 + 2 * 3 + 3 ^ 2) ^ 2 :=
  gtail_seven_shell 2 3 4 1 (by norm_num)

-- Independent direct finite-sum/arithmetic evaluation of both sides.
example : (1 : ℕ) * GTail 7 1 1 4 + 4 ^ 7 = 78125 := by
  decide

example : (2 : ℕ) ^ 7 + 3 ^ 7 +
    7 * 2 * 3 * (2 + 3) * (2 ^ 2 + 2 * 3 + 3 ^ 2) ^ 2 = 78125 := by
  norm_num

example {R : Type*} [CommSemiring R] (b c g : R) (h : 0 + b = c + g) :
    g * GTail 7 1 g c + c ^ 7 = b ^ 7 := by
  simpa using gtail_seven_shell (0 : R) b c g h

example {R : Type*} [CommSemiring R] (a c g : R) (h : a + 0 = c + g) :
    g * GTail 7 1 g c + c ^ 7 = a ^ 7 := by
  simpa using gtail_seven_shell a (0 : R) c g h

-- Reconstruct the conditional result independently using the mandated route.
example {a b c g : ℕ} (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  have h := gtail_seven_shell a b c g hsum
  change a ^ 7 + b ^ 7 = c ^ 7 at hEq
  rw [hEq, add_comm (c ^ 7)] at h
  exact Nat.add_right_cancel h

-- A satisfiable boundary Fermat equation tests the public conditional adapter.
example : (0 : ℕ) * GTail 7 1 0 3 =
    7 * 0 * 3 * (0 + 3) * (0 ^ 2 + 0 * 3 + 3 ^ 2) ^ 2 :=
  gtail_seven_eq_of_fermat7Equation (by norm_num [Fermat7Equation]) (by norm_num)

example {a b c g : ℕ} (h : CounterexamplePack a b c)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  gtail_seven_eq_of_counterexamplePack h hsum

example {R : Type*} [CommRing R] (a b c g : R) (h : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 +
        (a ^ 7 + b ^ 7 - c ^ 7) :=
  gtail_seven_defect a b c g h

#print axioms gtail_seven_shell
#print axioms gtail_seven_defect
#print axioms gtail_seven_eq_of_fermat7Equation
#print axioms gtail_seven_eq_of_counterexamplePack

end DkMathTest.FLT.Seven.GTailBridge
