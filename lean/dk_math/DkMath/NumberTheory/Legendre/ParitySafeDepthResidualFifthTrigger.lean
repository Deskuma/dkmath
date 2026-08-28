/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier

#print "file: DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger"

/-!
## ParitySafeDepthResidualFifthTrigger

PRIM-L066 separates the exact depth residual-pair capacity into the baseline
contributed by a four-support collision and the genuinely higher-support
remainder.  The latter is supported exactly on collision seats with at least
five active support primes.  Substituting this identity into the L065
full-cover frontier isolates the precise point at which a fifth direction
would become relevant.

This module does not construct a fifth-direction descent or counting theory.
It also does not prove full cover, estimate any finite capacity, or derive a
Legendre/RH conclusion.
-/

open scoped BigOperators

namespace DkMath.NumberTheory.Legendre

noncomputable section
local instance classicalDecidableFifthTrigger (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### PRIM-L066.1: the local four-support baseline -/

private theorem choose_two_ge_three_of_three_le (k : ℕ)
    (hk : 3 ≤ k) : 3 ≤ Nat.choose k 2 := by
  have hmono := Nat.choose_mono 2 hk
  have hbase : 3 ≤ Nat.choose 3 2 := by norm_num
  exact hbase.trans hmono

private theorem choose_two_ge_four_of_four_le (k : ℕ)
    (hk : 4 ≤ k) : 4 ≤ Nat.choose k 2 := by
  have hmono := Nat.choose_mono 2 hk
  have hbase : 4 ≤ Nat.choose 4 2 := by norm_num [Nat.choose]
  exact hbase.trans hmono

/-- A collision seat leaves at least the two-unit four-support baseline. -/
theorem paritySafeDepthResidualLocalCapacity_ge_two_of_collision
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    2 ≤ Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1 := by
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  have hthree : 3 ≤ (paritySafeActiveSupport n r).card - 1 := by omega
  have hchoose := choose_two_ge_three_of_three_le _ hthree
  omega

/-! ### PRIM-L066.2: higher-support residual -/

/-- The part of collision residual capacity beyond the four-support baseline. -/
noncomputable def paritySafeRechargeExactDepthHigherSupportResidualExcess
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3)

/-- Each collision residual is exactly baseline two plus its higher-support
remainder. -/
theorem paritySafeDepthResidualLocalCapacity_eq_two_add_higher
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1 =
      2 + (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3) := by
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  have hthree : 3 ≤ (paritySafeActiveSupport n r).card - 1 := by omega
  have hchoose := choose_two_ge_three_of_three_le _ hthree
  omega

/-! ### PRIM-L066.3: exact global baseline decomposition -/

/-- Exact decomposition of depth residual capacity into two per collision and
the higher-support remainder. -/
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_twoCollision_add_higherSupport
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      2 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  unfold paritySafeRechargeExactDepthResidualPairCapacityExcess
    paritySafeRechargeExactDepthHigherSupportResidualExcess
  calc
    (∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1)) =
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          (2 + (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact paritySafeDepthResidualLocalCapacity_eq_two_add_higher hr
    _ = (∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 2) +
          ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
            (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by simp [Nat.mul_comm]

/-! ### PRIM-L066.4: genuine five-direction collision seats -/

/-- Collision seats whose active support has at least five primes. -/
noncomputable def paritySafeRechargeExactDepthFiveDirectionCollisionSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthFiberCollisionSeats n).filter
    (fun r => 5 ≤ (paritySafeActiveSupport n r).card)

@[simp] theorem mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats
    {n r : ℕ} :
    r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ↔
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      5 ≤ (paritySafeActiveSupport n r).card := by
  simp [paritySafeRechargeExactDepthFiveDirectionCollisionSeats]

theorem paritySafeRechargeExactDepthFiveDirectionCollisionSeats_subset_collision
    (n : ℕ) :
    paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ⊆
      paritySafeRechargeExactDepthFiberCollisionSeats n := by
  intro r hr
  exact (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).1

/-! ### PRIM-L066.5: local higher-support trigger -/

/-- On a collision seat, the higher-support residual vanishes exactly at
support cardinality four. -/
theorem paritySafeDepthHigherResidual_eq_zero_iff_support_card_eq_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3 = 0 ↔
      (paritySafeActiveSupport n r).card = 4 := by
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  constructor
  · intro hzero
    by_contra hne
    have hfive : 5 ≤ (paritySafeActiveSupport n r).card := by omega
    have hfourminus : 4 ≤ (paritySafeActiveSupport n r).card - 1 := by omega
    have hchoose := choose_two_ge_four_of_four_le _ hfourminus
    omega
  · intro hcard
    have hchoose : Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 = 3 := by
      rw [hcard]
      norm_num
    omega

/-- The higher-support residual is positive exactly when a fifth support
prime is present. -/
theorem paritySafeDepthHigherResidual_pos_iff_support_card_ge_five
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    0 < Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3 ↔
      5 ≤ (paritySafeActiveSupport n r).card := by
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  constructor
  · intro hpos
    by_contra hnot
    have hcard : (paritySafeActiveSupport n r).card = 4 := by omega
    have hzero :=
      (paritySafeDepthHigherResidual_eq_zero_iff_support_card_eq_four hr).mpr hcard
    omega
  · intro hfive
    have hfourminus : 4 ≤ (paritySafeActiveSupport n r).card - 1 := by omega
    have hchoose := choose_two_ge_four_of_four_le _ hfourminus
    omega

/-! ### PRIM-L066.6: global support and trigger criterion -/

/-- The higher-support residual is supported exactly on five-direction seats. -/
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_fiveDirection_sum
    (n : ℕ) :
    paritySafeRechargeExactDepthHigherSupportResidualExcess n =
      ∑ r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n,
        (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3) := by
  unfold paritySafeRechargeExactDepthHigherSupportResidualExcess
  symm
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro r hr hnot
    have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
    have hlt : (paritySafeActiveSupport n r).card < 5 := by
      by_contra hge
      apply hnot
      exact mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mpr
        ⟨hr, le_of_not_gt hge⟩
    have hcard : (paritySafeActiveSupport n r).card = 4 := by omega
    exact (paritySafeDepthHigherResidual_eq_zero_iff_support_card_eq_four hr).mpr hcard

/-- No five-support collision is equivalent to zero higher-support residual. -/
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision
    (n : ℕ) :
    paritySafeRechargeExactDepthHigherSupportResidualExcess n = 0 ↔
      paritySafeRechargeExactDepthFiveDirectionCollisionSeats n = ∅ := by
  constructor
  · intro hzero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hsum := paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_fiveDirection_sum n
    rw [hzero] at hsum
    have hnonneg : ∀ x ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n,
        0 ≤ Nat.choose ((paritySafeActiveSupport n x).card - 1) 2 - 3 := by
      intro x hx
      exact Nat.zero_le _
    have hle := Finset.single_le_sum hnonneg hr
    have hpos := (paritySafeDepthHigherResidual_pos_iff_support_card_ge_five
      (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).1).mpr
      (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).2
    exact (by omega : False)
  · intro hempty
    rw [paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_fiveDirection_sum, hempty]
    simp

/-! ### PRIM-L066.8: sharpened full-cover frontier -/

/-- Full-cover frontier with the four-direction collision baseline and the
remaining higher-support residual displayed separately. -/
theorem two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  have hfront :=
    two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_fullCoverCapacity hn hfull
  have hdecomp := paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_twoCollision_add_higherSupport n
  omega

/-- Reduced quotient-interval form of the sharpened full-cover frontier. -/
theorem two_mul_pairOverlap_add_threeTotient_le_reducedQuotient_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  have hfront :=
    two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

/-! ### PRIM-L066.9: no-fifth-direction corollary -/

/-- If no collision seat has five active support primes, the sharpened
frontier carries only the minimal four-direction collision tax. -/
theorem two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_of_no_fiveDirectionCollision
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hfive : paritySafeRechargeExactDepthFiveDirectionCollisionSeats n = ∅) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
  have hfront :=
    two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual hn hfull
  have hzero :=
    paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision n
  rw [hzero.mpr hfive] at hfront
  omega

end
end DkMath.NumberTheory.Legendre
