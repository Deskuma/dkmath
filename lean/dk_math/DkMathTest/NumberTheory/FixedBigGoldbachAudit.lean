/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMathTest.NumberTheory.FixedBigGaugeAudit
import DkMathTest.NumberTheory.GoldbachGNFiber
import DkMath.NumberTheory.FixedBigGauge.Goldbach
import DkMath.NumberTheory.FixedBigGauge.BoundedChildren
import DkMath.NumberTheory.Primitive.PHZ30

namespace DkMathTest.FixedBigGoldbachAudit

open DkMath.NumberTheory
open DkMath.NumberTheory.FixedBigGauge
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimeGauge

/-- Full phase count is five, but this parent has no actual Goldbach seat. -/
theorem phase_count_does_not_supply_visible_child :
    (pairedSurvivingChildIndices 10 primeWorld235 7 29).card = 5 ∧
      boundedChildIndices 10 30 29 7 = ∅ := by
  constructor
  · exact pairedSurvivingChildIndices_card_eq_q_sub_two
      knownPrimeScales_primeWorld235 (by norm_num) (by decide +kernel)
      (by norm_num) (by norm_num)
  · decide +kernel

/-- The empty-parent countermodel persists under every positive fixed-Big gauge. -/
theorem scaled_countermodel {R : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    ∀ j : ℕ, ¬ ((29 + j * 30 : ℕ) * fixedBigUnit R k <
      (10 - 1 : ℕ) * fixedBigUnit R k) := by
  intro j
  rw [scaled_child_in_interval_iff hR hk]
  omega

/-- Growing the visible interval does not make moving-hole survival monotone. -/
theorem moving_holes_can_remove_last_visible_survivor :
    (boundedChildIndices 12 30 1 7 \ pairedReservedChildIndices 12 primeWorld235 7 1) = {0} ∧
      (boundedChildIndices 13 30 1 7 \ pairedReservedChildIndices 13 primeWorld235 7 1) = ∅ := by
  decide +kernel

/-- Three visible seats make the fresh-prime-only existence theorem concrete. -/
theorem three_visible_seats_supply_fresh_survivor :
    (boundedChildIndices 100 30 1 7 \ pairedReservedChildIndices 100 primeWorld235 7 1).Nonempty := by
  apply bounded_paired_survivor knownPrimeScales_primeWorld235
    (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
  have h := three_le_bounded_card (n := 100) (M := 30) (r := 1) (q := 7)
    (by omega) (by omega)
  simpa only [primeWorldModulus_primeWorld235] using (show 2 < (boundedChildIndices 100 30 1 7).card by omega)

/-- Mirror symmetry of the 30-wheel does not imply symmetry of prime labels. -/
theorem square_fold_does_not_preserve_primality :
    squareBody 30 = 960 ∧ 479 + 481 = 960 ∧
      Nat.Coprime 479 30 ∧ Nat.Coprime 481 30 ∧
      Nat.Prime 479 ∧ ¬ Nat.Prime 481 := by
  decide +kernel

/-- Choosing resolution two at edge ten turns both physical labels into ten. -/
theorem gauge_pair_can_have_composite_physical_lengths :
    GaugePrimePairAt 10 2 ∧
      (2 : ℝ) * fixedBigUnit 10 2 = 10 ∧ ¬ Nat.Prime 10 := by
  refine ⟨(gaugePrimePairAt_iff (by norm_num) (by omega)).mpr ?_, ?_, by norm_num⟩
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩
  · norm_num [fixedBigUnit]

/-- Reuse the existing kernel certificate at the original natural centers. -/
theorem original_gauge_centers_two_through_one_hundred :
    ∀ n ∈ Finset.range 101, 2 ≤ n → GaugePrimePairAt (n : ℝ) n := by
  intro n hn htwo
  apply (gaugePrimePairAt_iff (by exact_mod_cast (show 0 < n by omega)) (by omega)).mpr
  exact DkMathTest.NumberTheory.GoldbachGNFiber.goldbach_centers_two_through_one_hundred n hn htwo

end DkMathTest.FixedBigGoldbachAudit

-- Full audit of every theorem added in this checkpoint series.
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_pos
#print axioms DkMath.NumberTheory.FixedBigGauge.scale_unit_conservation
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBig_decomposition
#print axioms DkMath.NumberTheory.FixedBigGauge.unit_eq_iff_scale_mul_eq
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_div_edge
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_div_edge_eq_projectionGap
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_div_edge_eq_regularPhaseStep
#print axioms DkMath.NumberTheory.FixedBigGauge.normalized_unit_bounds
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBig_squareBody_normalization
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_transport
#print axioms DkMath.NumberTheory.FixedBigGauge.fixedBigUnit_refinement
#print axioms DkMath.NumberTheory.FixedBigGauge.world_unit_eq_edge_mul_projectionGap
#print axioms DkMath.NumberTheory.FixedBigGauge.freshPrime_fixedBigUnit_refinement
#print axioms DkMath.NumberTheory.FixedBigGauge.mem_boundedChildIndices
#print axioms DkMath.NumberTheory.FixedBigGauge.boundedChildIndices_initial
#print axioms DkMath.NumberTheory.FixedBigGauge.boundedChildIndices_eq_zero_of_large_modulus
#print axioms DkMath.NumberTheory.FixedBigGauge.boundedChildIndices_succ
#print axioms DkMath.NumberTheory.FixedBigGauge.bounded_survivors_add_reserved
#print axioms DkMath.NumberTheory.FixedBigGauge.bounded_survivor_of_two_holes
#print axioms DkMath.NumberTheory.FixedBigGauge.three_le_bounded_card
#print axioms DkMath.NumberTheory.FixedBigGauge.bounded_paired_survivor
#print axioms DkMath.NumberTheory.FixedBigGauge.scaled_sum_eq_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.gaugePrimePairAt_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.exists_gaugePrimePairAt
#print axioms DkMath.NumberTheory.FixedBigGauge.resolution_eq_original_of_preserved_sum
#print axioms DkMath.NumberTheory.FixedBigGauge.unit_eq_one_of_preserved_sum
#print axioms DkMath.NumberTheory.FixedBigGauge.original_gauge_iff_capacity
#print axioms DkMath.NumberTheory.FixedBigGauge.strongGoldbach_iff_original_gauge
#print axioms DkMath.NumberTheory.FixedBigGauge.prime_scaled_label_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.scaled_lt_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.scaled_child_in_interval_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell
#print axioms DkMath.NumberTheory.FixedBigGauge.prime_iff_coprime_in_squareShell
#print axioms DkMath.NumberTheory.FixedBigGauge.scaled_le_iff
#print axioms DkMath.NumberTheory.FixedBigGauge.prime_iff_coprime_of_physical_squareShell
#print axioms DkMathTest.FixedBigGaugeAudit.lower_bound_is_necessary
#print axioms DkMathTest.FixedBigGaugeAudit.next_square_counterexample
#print axioms DkMathTest.FixedBigGaugeAudit.incomplete_world_counterexample
#print axioms DkMathTest.FixedBigGaugeAudit.zero_edge_counterexample
#print axioms DkMathTest.FixedBigGaugeAudit.composite_direction_arithmetic
#print axioms DkMathTest.FixedBigGoldbachAudit.phase_count_does_not_supply_visible_child
#print axioms DkMathTest.FixedBigGoldbachAudit.scaled_countermodel
#print axioms DkMathTest.FixedBigGoldbachAudit.moving_holes_can_remove_last_visible_survivor
#print axioms DkMathTest.FixedBigGoldbachAudit.three_visible_seats_supply_fresh_survivor
#print axioms DkMathTest.FixedBigGoldbachAudit.square_fold_does_not_preserve_primality
#print axioms DkMathTest.FixedBigGoldbachAudit.gauge_pair_can_have_composite_physical_lengths
#print axioms DkMathTest.FixedBigGoldbachAudit.original_gauge_centers_two_through_one_hundred
