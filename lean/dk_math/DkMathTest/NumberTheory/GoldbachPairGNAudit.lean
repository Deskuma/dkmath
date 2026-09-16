/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.Goldbach.PairGNCubic

namespace DkMathTest.GoldbachPairGNAudit

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory
open DkMath.NumberTheory.GoldbachPairGN

theorem prime_degree_is_not_sufficient :
    Nat.Prime 3 ∧ GN 3 1 5 = 91 ∧ 91 = 7 * 13 ∧ ¬ Nat.Prime (GN 3 1 5) := by
  rw [cubic_unit]
  norm_num

/-- Both entries satisfy the circle exactly and both are composite. -/
theorem circle_geometry_does_not_certify_primes :
    pairBody 3 3 5 5 = 2 * 91 ∧
      8 * 91 - 2 = 3 * ((2 * 5 + 1) ^ 2 + (2 * 5 + 1) ^ 2) ∧
      ¬ Nat.Prime (GN 3 1 5) := by
  unfold pairBody
  rw [cubic_unit]
  norm_num

/-- Prime labels and the weighted equation still do not supply a cubic parameter. -/
theorem weighted_prime_labels_do_not_supply_cubic_lift :
    Nat.Prime 3 ∧ Nat.Prime 13 ∧ 3 = 1 + 2 * 1 ∧ 13 = 1 + 3 * 4 ∧
      2 * 1 + 3 * 4 = 2 * (8 - 1) ∧ ¬ ∃ v : ℕ, GN 3 1 v = 13 := by
  exact ⟨by norm_num, by norm_num, by omega, by omega, by omega, thirteen_not_in_cubic_row⟩

theorem degree_two_does_not_represent_two : ¬ ∃ u : ℕ, GN 2 1 u = 2 := by
  rintro ⟨u, hu⟩
  rw [goldbach_GN_two] at hu
  omega

theorem positive_pair_cannot_represent_target_four {d e : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) : ¬ UnitPairAt 2 d e := by
  rintro ⟨u, v, hu, hv, _, _, hsum⟩
  have hl : GNPositiveRepresentation (GN d 1 u) d 1 u := ⟨hd, by omega, hu, rfl⟩
  have hr : GNPositiveRepresentation (GN e 1 v) e 1 v := ⟨he, by omega, hv, rfl⟩
  have hlb := hl.bounds.2.2.2.1
  have hrb := hr.bounds.2.2.2.1
  change GN d 1 u + GN e 1 v = 2 * 2 at hsum
  omega

/-- Requiring strictly different prime degrees also loses the 3+3 target. -/
theorem strict_degree_asymmetry_misses_six :
    ¬ ∃ d e : ℕ, Nat.Prime d ∧ Nat.Prime e ∧ d ≠ e ∧ UnitPairAt 3 d e := by
  rintro ⟨d, e, hd, he, hne, u, v, hu, hv, _, _, hsum⟩
  have hl : GNPositiveRepresentation (GN d 1 u) d 1 u := ⟨hd.two_le, by omega, hu, rfl⟩
  have hr : GNPositiveRepresentation (GN e 1 v) e 1 v := ⟨he.two_le, by omega, hv, rfl⟩
  have hlb := hl.bounds.2.2.2.1
  have hrb := hr.bounds.2.2.2.1
  have hd2 := hd.two_le
  have he2 := he.two_le
  change GN d 1 u + GN e 1 v = 2 * 3 at hsum
  omega

/-- Sixteen is Goldbach, but neither orientation of the mixed row represents it. -/
theorem mixed_pair_is_strictly_restrictive :
    GoldbachPairAt 8 ∧ ¬ UnitPairAt 8 2 3 ∧ ¬ UnitPairAt 8 3 2 := by
  have hnot : ¬ UnitPairAt 8 2 3 := not_unitPairAt_two_three_of_mod_nine (by omega)
  refine ⟨⟨3, 13, by norm_num, by norm_num, by omega⟩, hnot, ?_⟩
  exact fun h => hnot ((unitPairAt_swap 8 3 2).mp h)

/-- Twenty-eight gives a second failure even outside the 8 modulo 9 obstruction. -/
theorem mixed_pair_misses_twenty_eight : GoldbachPairAt 14 ∧ ¬ UnitPairAt 14 2 3 := by
  refine ⟨⟨5, 23, by norm_num, by norm_num, by omega⟩, ?_⟩
  intro h
  obtain ⟨v, _, hp, hsum⟩ := (unitPairAt_two_three_iff_on_mod_three (by omega : 14 % 3 = 2)).mp h
  have heq : GN 3 1 v = 25 := by omega
  rw [heq] at hp
  norm_num at hp

theorem mixed_pair_positive_example : UnitPairAt 5 2 3 := by
  refine ⟨1, 1, by omega, by omega, ?_, ?_, ?_⟩
  · rw [goldbach_GN_two]; norm_num
  · rw [cubic_unit]; norm_num
  · rw [pairBody, goldbach_GN_two, cubic_unit]; norm_num

theorem cubic_pair_positive_example : UnitPairAt 7 3 3 := by
  refine ⟨1, 1, by omega, by omega, ?_, ?_, ?_⟩
  · rw [cubic_unit]; norm_num
  · rw [cubic_unit]; norm_num
  · rw [pairBody, cubic_unit]; norm_num

/-- The modeling choice is not a universal prohibition on equality to any single Big. -/
theorem goldbach_target_can_equal_a_single_big :
    GoldbachPairAt 8 ∧ 2 * 8 = (1 + 3) ^ 2 := by
  exact ⟨⟨3, 13, by norm_num, by norm_num, by omega⟩, by norm_num⟩

end DkMathTest.GoldbachPairGNAudit

-- Audit of every theorem added for the two-universe proposal.
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_add_pairGap
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBig_sub_pairGap
#print axioms DkMath.NumberTheory.GoldbachPairGN.singleBig_sub_GN
#print axioms DkMath.NumberTheory.GoldbachPairGN.single_complement_not_prime
#print axioms DkMath.NumberTheory.GoldbachPairGN.prime_unitGN_constraints
#print axioms DkMath.NumberTheory.GoldbachPairGN.prime_unitGN_quotient
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_eq_iff_weighted_quotients
#print axioms DkMath.NumberTheory.GoldbachPairGN.unitPairAt_swap
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_lt_pairBig
#print axioms DkMath.NumberTheory.GoldbachPairGN.goldbachPairAt_of_unitPairAt
#print axioms DkMath.NumberTheory.GoldbachPairGN.exists_unitGN_two_of_odd_prime
#print axioms DkMath.NumberTheory.GoldbachPairGN.prime_pair_odd
#print axioms DkMath.NumberTheory.GoldbachPairGN.goldbachPairAt_iff_unitPairAt_two_two
#print axioms DkMath.NumberTheory.GoldbachPairGN.exists_prime_degrees_iff_goldbach
#print axioms DkMath.NumberTheory.GoldbachPairGN.strongGoldbach_iff_unitPairAt_two_two
#print axioms DkMath.NumberTheory.GoldbachPairGN.cubic_unit
#print axioms DkMath.NumberTheory.GoldbachPairGN.cubic_unit_quotient
#print axioms DkMath.NumberTheory.GoldbachPairGN.cubic_quotient_eq_iff
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_three_three_eq_iff
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_three_three_eq_iff_circle
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_three_three_eq_iff_circle_sub
#print axioms DkMath.NumberTheory.GoldbachPairGN.center_mod_three_of_cubic_pair
#print axioms DkMath.NumberTheory.GoldbachPairGN.pairBody_two_three_eq_iff
#print axioms DkMath.NumberTheory.GoldbachPairGN.mixed_left_parameter_eq_one
#print axioms DkMath.NumberTheory.GoldbachPairGN.unitPairAt_two_three_iff_on_mod_three
#print axioms DkMath.NumberTheory.GoldbachPairGN.cubic_unit_mod_nine
#print axioms DkMath.NumberTheory.GoldbachPairGN.not_unitPairAt_two_three_of_mod_nine
#print axioms DkMath.NumberTheory.GoldbachPairGN.mixed_degrees_miss_progression
#print axioms DkMath.NumberTheory.GoldbachPairGN.thirteen_not_in_cubic_row
#print axioms DkMathTest.GoldbachPairGNAudit.prime_degree_is_not_sufficient
#print axioms DkMathTest.GoldbachPairGNAudit.circle_geometry_does_not_certify_primes
#print axioms DkMathTest.GoldbachPairGNAudit.weighted_prime_labels_do_not_supply_cubic_lift
#print axioms DkMathTest.GoldbachPairGNAudit.degree_two_does_not_represent_two
#print axioms DkMathTest.GoldbachPairGNAudit.positive_pair_cannot_represent_target_four
#print axioms DkMathTest.GoldbachPairGNAudit.strict_degree_asymmetry_misses_six
#print axioms DkMathTest.GoldbachPairGNAudit.mixed_pair_is_strictly_restrictive
#print axioms DkMathTest.GoldbachPairGNAudit.mixed_pair_misses_twenty_eight
#print axioms DkMathTest.GoldbachPairGNAudit.mixed_pair_positive_example
#print axioms DkMathTest.GoldbachPairGNAudit.cubic_pair_positive_example
#print axioms DkMathTest.GoldbachPairGNAudit.goldbach_target_can_equal_a_single_big
