/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionModSixResidues"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven DkMath.CosmicFormulaBinom

example {x y : ℕ} (h : Nat.Coprime x y) :
    Nat.ModEq 6 (alternatingCyclotomicSeven x y) 1 :=
  alternatingCyclotomicSeven_mod_six_of_coprime h

example {D u : ℕ} (h : Nat.Coprime D u) : Nat.ModEq 6 (GN 7 D u) 1 :=
  GN_seven_mod_six_of_coprime h

-- Zero endpoints are included; positivity is unnecessary.
example : Nat.ModEq 6 (alternatingCyclotomicSeven 0 1) 1 :=
  alternatingCyclotomicSeven_mod_six_of_coprime (by decide)
example : Nat.ModEq 6 (GN 7 1 0) 1 :=
  GN_seven_mod_six_of_coprime (by decide)
example : Nat.ModEq 6 (GN 7 2 3) 1 :=
  GN_seven_mod_six_of_coprime (by decide)
example : Nat.ModEq 6 (alternatingCyclotomicSeven 2 3) 1 :=
  alternatingCyclotomicSeven_mod_six_of_coprime (by decide)

-- Coprimality cannot simply be dropped from the universal statements.
example : ¬ Nat.ModEq 6 (alternatingCyclotomicSeven 2 2) 1 := by decide
example : ¬ Nat.ModEq 6 (GN 7 2 2) 1 := by
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  decide

-- Residue one does not imply coprimality, hence is only a necessary filter.
example : ¬ Nat.Coprime 5 5 ∧
    Nat.ModEq 6 (alternatingCyclotomicSeven 5 5) 1 ∧
    Nat.ModEq 6 (GN 7 5 5) 1 := by
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  decide

#print axioms DkMath.FLT.Seven.alternatingCyclotomicSeven_mod_six_of_coprime
#print axioms DkMath.FLT.Seven.GN_seven_mod_six_of_coprime
end DkMathTest.FLT.Seven
