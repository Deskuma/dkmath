/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven

#print "file: DkMathTest.FLT.Seven.GTailFacade"

/-!
Public FLT7 import smoke tests. The shell needs no Fermat premise; positive
conditional theorem types below do not fabricate a positive Fermat solution.
-/

namespace DkMathTest.FLT.Seven.GTailFacade

open DkMath.CosmicFormula DkMath.FLT.Seven

example {R : Type*} [CommSemiring R] (a b c g : R) (hsum : a + b = c + g) :
    g * GTail 7 1 g c + c ^ 7 = (a ^ 7 + b ^ 7) +
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  gtail_seven_shell a b c g hsum

example : (1 : ℕ) * GTail 7 1 1 4 + 4 ^ 7 =
    (2 ^ 7 + 3 ^ 7) + 7 * 2 * 3 * (2 + 3) * (2 ^ 2 + 2 * 3 + 3 ^ 2) ^ 2 :=
  gtail_seven_shell 2 3 4 1 (by norm_num)

example {a b c g : ℕ} (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  gtail_seven_eq_of_fermat7Equation hEq hsum

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c) :
    ∃ g : ℕ, 0 < g ∧ g < a ∧ g < b ∧ c + g = a + b :=
  exists_positive_focused_gap ha hb hEq

example {a b c g : ℕ} (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    7 ∣ g := seven_dvd_focused_gap hEq hsum

#print axioms gtail_seven_shell
#print axioms gtail_seven_eq_of_fermat7Equation
#print axioms exists_positive_focused_gap
#print axioms seven_dvd_focused_gap

end DkMathTest.FLT.Seven.GTailFacade
