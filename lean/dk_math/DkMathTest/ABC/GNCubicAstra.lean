/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNCubicOrientation
import DkMath.ABC.GNCubicBoundaryWeight
import DkMath.ABC.GNCubicPairedDepth
import DkMath.ABC.GNExcessProfileOvercount

#print "file: DkMathTest.ABC.GNCubicAstra"

/-! Numeric regressions and dependency audits for ASTRA-001. -/
namespace DkMathTest.ABC.GNCubicAstra
open DkMath.ABC DkMath.NumberTheory DkMath.CosmicFormulaBinom

-- The ordinary prime 7 can occur in both orientations with unequal depths.
example : Nat.Coprime 605 370688 ∧
    GN 3 (605 : ℕ) 370688 = 7 * 37^2 * 1777 * 24247 ∧
    GN 3 (370688 : ℕ) 605 = 7^3 * 41413 * 9721 := by
  simp only [GN_three_dual_explicit]
  norm_num [Nat.coprime_iff_gcd_eq_one]

example : Nat.Prime 7 ∧ Nat.Prime 37 ∧ Nat.Prime 1777 ∧
    Nat.Prime 24247 ∧ Nat.Prime 41413 ∧ Nat.Prime 9721 := by norm_num

-- Neither orientation is forced to be Wieferich-free.
example : GNWieferichLift 3 11 40 79 ∧ GNWieferichLift 3 40 11 7 := by
  simp only [GNWieferichLift, GN_three_dual_explicit]
  norm_num

-- Both repeated moduli can exceed the same interval threshold.
example : Nat.Coprime 56 59 ∧ GN 3 (56 : ℕ) 59 = 13^2*139 ∧
    GN 3 (59 : ℕ) 56 = 151^2 ∧
    56+59+1 < (13 : ℕ)^2 ∧ 56+59+1 < (151 : ℕ)^2 := by
  simp only [GN_three_dual_explicit]
  norm_num [Nat.coprime_iff_gcd_eq_one]

-- Exact, independently chosen depths 2 and 3 in opposite orientations.
example : 7^2 ∣ GN 3 (1713314 : ℕ) 1 ∧ ¬ 7^3 ∣ GN 3 (1713314 : ℕ) 1 ∧
    13^3 ∣ GN 3 (1 : ℕ) 1713314 ∧ ¬ 13^4 ∣ GN 3 (1 : ℕ) 1713314 := by
  simp only [GN_three_dual_explicit]
  norm_num

-- In one orientation each requested depth fits, but their product does not.
example : (7 : ℕ)^2 ≤ GN 3 (13 : ℕ) 1 ∧
    (13 : ℕ)^2 ≤ GN 3 (13 : ℕ) 1 ∧ 3*(13+1)^2 < (7 : ℕ)^2*13^2 := by
  simp only [GN_three_dual_explicit]
  norm_num

#print axioms DkMath.NumberTheory.GN_three_orientation_bezout
#print axioms DkMath.NumberTheory.GN_three_orientation_bezout_swap
#print axioms DkMath.NumberTheory.gcd_GN_three_swap_dvd_fourteen
#print axioms DkMath.NumberTheory.not_prime_sq_dvd_both_GN_three
#print axioms DkMath.NumberTheory.GN_three_modEq
#print axioms DkMath.NumberTheory.exists_GN_three_unit_pow_root
#print axioms DkMath.NumberTheory.exists_GN_three_unit_exact_depth
#print axioms DkMath.NumberTheory.GN_three_three_mul_unit
#print axioms DkMath.NumberTheory.exists_GN_three_swapped_unit_exact_depth
#print axioms DkMath.NumberTheory.exists_GN_three_pair_exact_depth_progression
#print axioms DkMath.NumberTheory.exists_GN_three_seven_thirteen_exact_depth_progression
#print axioms DkMath.NumberTheory.exists_large_GN_three_seven_thirteen_exact_depth
#print axioms DkMath.ABC.GNNonExceptionalWieferichPrimeSet_three_disjoint_swap
#print axioms DkMath.ABC.GNNonExceptionalRepeatedPart_three_coprime_swap
#print axioms DkMath.ABC.seven_le_prime_of_mod_three_eq_one
#print axioms DkMath.ABC.GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths
#print axioms DkMath.ABC.prime_pow_dvd_GNNonExceptionalRepeatedPart
#print axioms DkMath.ABC.exists_arbitrarily_large_coprime_cubic_repeated_parts
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_active
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_modulus
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_mass
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_local_depth_fits
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_modulus_gt_cubic_bound
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_mem_large
#print axioms DkMath.ABC.GNExcessTwoPrimeProfile_event_eq_empty
#print axioms DkMath.ABC.GNExcessLargeBoundaryProfileSum_ge_two_prime_profile
#print axioms DkMath.ABC.seven_thirteen_mem_GNNonExceptionalIntervalPrimeFamily_three
#print axioms DkMath.ABC.GNExcessLargeBoundaryProfileSum_three_eighths_ge_geometric
#print axioms DkMath.ABC.not_exists_GNExcess_cubic_largeBoundary_linear_bound
#print axioms DkMath.ABC.GNExcess_cubic_realized_modulus_le_height

end DkMathTest.ABC.GNCubicAstra
