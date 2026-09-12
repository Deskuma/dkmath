/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach

#print "file: DkMathTest.NumberTheory.GoldbachCrossGapExchangeAudit"

/-!
# Cross-Gap Exchange regression and axiom audit

The numerical examples are standalone arithmetic sanity checks.  They are not
claimed to arise from particular Cosmic Formula coordinates.
-/

namespace DkMathTest.NumberTheory.GoldbachCrossGapExchangeAudit

open DkMath.NumberTheory.GoldbachCrossGapExchange

example : 10 + 20 = 13 + 17 := by norm_num

example : 8 + 2 = 7 + 3 := by norm_num

example : 120 + 8 = 109 + 19 := by norm_num

example (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ + crossRight d₁ x₁ u₁ d₂ x₂ u₂ =
      pairedBig d₁ x₁ u₁ d₂ x₂ u₂ := by
  exact crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂

example :
    crossLeft 2 3 1 3 4 2 = 23 ∧ crossRight 2 3 1 3 4 2 = 209 := by
  decide +kernel

example {p x u : ℕ} (hp : Nat.Prime p) (hx : ¬ p ∣ x) :
    crossGapBody p x u ≡ x [MOD p] := by
  exact crossGapBody_modEq_left_of_prime_degree hp hx

end DkMathTest.NumberTheory.GoldbachCrossGapExchangeAudit

#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossGapBody_add_crossGapGap_eq_crossGapBig
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.pairedBig_eq_bodies_add_gaps
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_add_crossRight_eq_pairedBig
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_swap_eq_crossRight
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossRight_swap_eq_crossLeft
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_eq_firstBig_of_gap_eq
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossRight_eq_secondBig_of_gap_eq
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_eq_crossRight_of_body_eq_of_gap_eq
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_intCast_eq_firstBig_add_transfer
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossRight_intCast_eq_secondBig_sub_transfer
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossGapBody_modEq_left_of_prime_degree
#print axioms DkMath.NumberTheory.GoldbachCrossGapExchange.crossLeft_modEq_left_add_foreignGap_of_prime_degree
