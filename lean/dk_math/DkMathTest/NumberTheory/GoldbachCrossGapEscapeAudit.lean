/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach

#print "file: DkMathTest.NumberTheory.GoldbachCrossGapEscapeAudit"

/-!
# Cross-Gap finite obstruction certification audit

These regressions keep coprimality separate from primality and keep the
diagonal prime pair separate from primitive-pair reasoning.
-/

namespace DkMathTest.NumberTheory.GoldbachCrossGapEscapeAudit

open DkMath.NumberTheory
open DkMath.NumberTheory.GoldbachCrossGapExchange
open DkMath.NumberTheory.GoldbachCrossGapEscape

/-- Coprime endpoints need not be prime endpoints. -/
example : 25 + 27 = 52 ∧ Nat.Coprime 25 27 ∧
    ¬ (Nat.Prime 25 ∧ Nat.Prime 27) := by
  norm_num [Nat.Coprime]

/-- The diagonal prime pair need not be coprime. -/
example : 3 + 3 = 6 ∧ ¬ Nat.Coprime 3 3 ∧
    Nat.Prime 3 ∧ Nat.Prime 3 := by
  norm_num [Nat.Coprime]

/-- A full-coordinate diagonal Cross-Gap configuration is an even fiber. -/
example : CrossGapEvenFiberAt 3 1 2 1 1 2 1 := by
  decide +kernel

/-- The same configuration survives its complete small-prime obstruction set. -/
example : CrossGapSurvives 3 1 2 1 1 2 1 := by
  decide +kernel

/-- One concrete Cross-Gap survivor closes to the local Goldbach statement. -/
example : GoldbachPairAt 3 := by
  refine goldbachPairAt_of_crossGapSurvives
    (d₁ := 1) (x₁ := 2) (u₁ := 1) (d₂ := 1) (x₂ := 2) (u₂ := 1) ?_ ?_
  · decide +kernel
  · decide +kernel

/-- The concrete configuration has the expected diagonal prime outputs. -/
example :
    crossLeft 1 2 1 1 2 1 = 3 ∧
      crossRight 1 2 1 1 2 1 = 3 ∧
      pairedBig 1 2 1 1 2 1 = 2 * 3 := by
  decide +kernel

end DkMathTest.NumberTheory.GoldbachCrossGapEscapeAudit

#print axioms DkMath.NumberTheory.GoldbachCrossGapEscape.crossLeft_le_even_target_of_fiber
#print axioms DkMath.NumberTheory.GoldbachCrossGapEscape.crossRight_le_even_target_of_fiber
#print axioms DkMath.NumberTheory.GoldbachCrossGapEscape.crossGap_not_prime_pair_iff_obstructed
#print axioms DkMath.NumberTheory.GoldbachCrossGapEscape.crossGapSurvives_iff_prime_pair
#print axioms DkMath.NumberTheory.GoldbachCrossGapEscape.goldbachPairAt_of_crossGapSurvives
