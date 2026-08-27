/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess"

/-!
## ParitySafeRechargeDepthFiberExcess

PRIM-L057 separates the exact depth pair mass into the mass of occupied L018
seats and the unpaid multiplicity of their pair fibers.  The excess is a
finite Nat sum of local terms `fiber.card - 1`; no global Nat subtraction is
introduced.

The module is a ledger refinement only.  It does not prove that fibers are
singletons, make the excess vanish, or extend the fourth direction into a
fifth direction.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableDepthFiberExcess (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L057.1: occupied fibers -/

/-- An occupied depth seat has a nonempty exact-pair fiber. -/
theorem paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).Nonempty := by
  rcases Finset.mem_image.mp hr with ⟨bt, hbt, hseat⟩
  refine ⟨bt, ?_⟩
  exact mem_paritySafeRechargeExactDepthPairsAtSeat.mpr ⟨hbt, hseat⟩

/-- The corresponding fiber cardinality is positive. -/
theorem paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthSeats n) :
    0 < (paritySafeRechargeExactDepthPairsAtSeat n r).card :=
  Finset.card_pos.mpr
    (paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hr)

/-! ### PRIM-L057.2: exact depth fiber excess -/

/-- The multiplicity not paid by the first copy of each occupied seat. -/
noncomputable def paritySafeRechargeExactDepthFiberExcess
  (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthSeats n,
    ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1)

@[simp] theorem paritySafeRechargeExactDepthFiberExcess_zero_of_empty_seats
    {n : ℕ}
    (hseats : paritySafeRechargeExactDepthSeats n = ∅) :
    paritySafeRechargeExactDepthFiberExcess n = 0 := by
  simp [paritySafeRechargeExactDepthFiberExcess, hseats]

/-- Exact depth pair mass is occupied-seat mass plus fiber excess. -/
theorem paritySafeRechargeExactDepthPairs_card_eq_seats_add_fiberExcess
    (n : ℕ) :
    (paritySafeRechargeExactDepthDualBasePairs n).card =
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  rw [paritySafeRechargeExactDepthPairs_card_eq_sum_seat_fibers]
  unfold paritySafeRechargeExactDepthFiberExcess
  calc
    ∑ r ∈ paritySafeRechargeExactDepthSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card =
        ∑ r ∈ paritySafeRechargeExactDepthSeats n,
          (1 + ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hpos :=
        paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats hr
      omega
    _ = (∑ _r ∈ paritySafeRechargeExactDepthSeats n, 1) +
          ∑ r ∈ paritySafeRechargeExactDepthSeats n,
            ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1) := by
      rw [Finset.sum_add_distrib]
    _ = (paritySafeRechargeExactDepthSeats n).card +
          ∑ r ∈ paritySafeRechargeExactDepthSeats n,
            ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1) := by
      simp

/-! ### PRIM-L057.3: collision seats -/

/-- Occupied seats whose exact-depth fiber contains at least two pairs. -/
noncomputable def paritySafeRechargeExactDepthFiberCollisionSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthSeats n).filter
    (fun r => 2 ≤ (paritySafeRechargeExactDepthPairsAtSeat n r).card)

@[simp] theorem mem_paritySafeRechargeExactDepthFiberCollisionSeats
    {n r : ℕ} :
    r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ↔
      r ∈ paritySafeRechargeExactDepthSeats n ∧
        2 ≤ (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  simp [paritySafeRechargeExactDepthFiberCollisionSeats]

/-- Fiber excess is supported exactly on collision seats. -/
theorem paritySafeRechargeExactDepthFiberExcess_eq_collision_sum
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n =
      ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1) := by
  unfold paritySafeRechargeExactDepthFiberExcess
  symm
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro r hr hcollision
    have hpos :=
      paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats hr
    have hlt : (paritySafeRechargeExactDepthPairsAtSeat n r).card < 2 := by
      by_contra hnot
      apply hcollision
      exact mem_paritySafeRechargeExactDepthFiberCollisionSeats.mpr
        ⟨hr, le_of_not_gt hnot⟩
    omega

/-- Zero excess is equivalent to every occupied fiber being a singleton. -/
theorem paritySafeRechargeExactDepthFiberExcess_eq_zero_iff
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n = 0 ↔
      ∀ r ∈ paritySafeRechargeExactDepthSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card = 1 := by
  constructor
  · intro hzero r hr
    have hpos :=
      paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats hr
    by_contra hne
    have htwo : 2 ≤ (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
      omega
    have hcollision :=
      mem_paritySafeRechargeExactDepthFiberCollisionSeats.mpr ⟨hr, htwo⟩
    have hle := Finset.single_le_sum
      (s := paritySafeRechargeExactDepthFiberCollisionSeats n)
      (f := fun q =>
        (paritySafeRechargeExactDepthPairsAtSeat n q).card - 1)
      (fun q hq => Nat.zero_le _) hcollision
    have hsum := paritySafeRechargeExactDepthFiberExcess_eq_collision_sum n
    rw [hzero] at hsum
    have hterm : 0 <
        (paritySafeRechargeExactDepthPairsAtSeat n r).card - 1 := by omega
    omega
  · intro hsingleton
    rw [paritySafeRechargeExactDepthFiberExcess_eq_collision_sum]
    apply Finset.sum_eq_zero
    intro r hr
    have hcard := hsingleton r
      (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
    omega

/-! ### PRIM-L057.4: paid/unpaid global ledgers -/

/-- Residual pair mass with exact depth split into paid seats and excess. -/
theorem paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafeResidualPairMass_eq_near_add_terminal_add_depth_add_fourth,
    paritySafeRechargeExactDepthPairs_card_eq_seats_add_fiberExcess]
  simp [Nat.add_assoc]

/-- Upper residual ledger after charging distinct depth seats to L018. -/
theorem paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n ≤
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth]
  have hbudget := paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget n
  omega

/-- The prime-pair overlap ledger with the same paid/unpaid depth refinement. -/
theorem paritySafePrimePairOverlapCount_le_supportExcess_add_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafePrimePairOverlapCount n ≤
      paritySafeSupportExcess n +
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafePrimePairOverlapCount_eq_supportExcess_add_residual]
  have hupper :=
    paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth n
  omega

/-! ### PRIM-L057.5: zero-excess frontier -/

/-- If no fiber multiplicity remains, all exact depth pairs fit the L018 budget. -/
theorem paritySafeRechargeExactDepthPairs_card_le_L018Depth_of_fiberExcess_eq_zero
    {n : ℕ}
    (hzero : paritySafeRechargeExactDepthFiberExcess n = 0) :
    (paritySafeRechargeExactDepthDualBasePairs n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  rw [paritySafeRechargeExactDepthPairs_card_eq_seats_add_fiberExcess, hzero,
    Nat.add_zero]
  exact paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget n

/-! ### PRIM-L057.6: arithmetic collision candidate -/

/-- Arithmetic data for the two n=58 depth pairs sharing seat 101. -/
theorem paritySafeRechargeExactDepthFiber_collision_arithmetic_58 :
    paritySafeRechargeExactSeat 58 15 21 = 101 ∧
      paritySafeRechargeExactSeat 58 21 15 = 101 ∧
      paritySafeRechargeOddShellQuotient 58 15 21 = 11 ∧
      paritySafeRechargeOddShellQuotient 58 21 15 = 11 := by
  norm_num [paritySafeRechargeExactSeat, paritySafeRechargeExactShellPoint,
    paritySafeRechargeOddShellQuotient]

/-- The two concrete n=58 exact depth pairs occupy the same seat. -/
theorem paritySafeRechargeExactDepthFiber_collision_witness_58 :
    (15, 21) ∈ paritySafeRechargeExactDepthDualBasePairs 58 ∧
      (21, 15) ∈ paritySafeRechargeExactDepthDualBasePairs 58 ∧
      paritySafeRechargeExactSeat 58 15 21 = 101 ∧
      paritySafeRechargeExactSeat 58 21 15 = 101 ∧
      2 ≤ (paritySafeRechargeExactDepthPairsAtSeat 58 101).card := by
  have hactive3 : 3 ∈ squareAnchorOddActivePrimes 58 := by
    apply mem_squareAnchorOddActivePrimes.mpr
    norm_num
  have hactive5 : 5 ∈ squareAnchorOddActivePrimes 58 := by
    apply mem_squareAnchorOddActivePrimes.mpr
    norm_num
  have hactive7 : 7 ∈ squareAnchorOddActivePrimes 58 := by
    apply mem_squareAnchorOddActivePrimes.mpr
    norm_num
  have hgate3 : 3 ∈ paritySafeTripleGatePrimes 58 := by
    apply mem_paritySafeTripleGatePrimes.mpr
    refine ⟨hactive3, ?_⟩
    norm_num [squareBody]
  have hbase15 : (15, 21) ∈
      paritySafeRechargeOverAnchorDualBasePairs 58 := by
    apply mem_paritySafeRechargeOverAnchorDualBasePairs.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply mem_paritySafeFarCofactorBaseOffsets.mpr
      norm_num
    · apply mem_paritySafeFarCofactorBaseOffsets.mpr
      norm_num
    · norm_num
  have hbase21 : (21, 15) ∈
      paritySafeRechargeOverAnchorDualBasePairs 58 := by
    apply mem_paritySafeRechargeOverAnchorDualBasePairs.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply mem_paritySafeFarCofactorBaseOffsets.mpr
      norm_num
    · apply mem_paritySafeFarCofactorBaseOffsets.mpr
      norm_num
    · norm_num
  have hadmiss15 : (15, 21) ∈
      paritySafeRechargePrimeAdmissibleDualBasePairs 58 := by
    apply mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mpr
    refine ⟨hbase15, ?_⟩
    norm_num [paritySafeRechargeOddShellQuotient]
  have hadmiss21 : (21, 15) ∈
      paritySafeRechargePrimeAdmissibleDualBasePairs 58 := by
    apply mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mpr
    refine ⟨hbase21, ?_⟩
    norm_num [paritySafeRechargeOddShellQuotient]
  have hwitness15 :
      ParitySafeRechargeExactPairWitness 58 15 21 3 5 := by
    refine ⟨hgate3, hactive5, by norm_num, by norm_num, ?_, ?_⟩
    · norm_num [paritySafeRechargeOddShellQuotient]
    · intro a ha halt hadiv
      have hprime := (mem_squareAnchorOddActivePrimes.mp ha).1
      have hne := (mem_squareAnchorOddActivePrimes.mp ha).2.2.2
      have htwo := hprime.two_le
      omega
  have hwitness21 :
      ParitySafeRechargeExactPairWitness 58 21 15 3 7 := by
    refine ⟨hgate3, hactive7, by norm_num, by norm_num, ?_, ?_⟩
    · norm_num [paritySafeRechargeOddShellQuotient]
    · intro a ha halt hadiv
      have hprime := (mem_squareAnchorOddActivePrimes.mp ha).1
      have hne := (mem_squareAnchorOddActivePrimes.mp ha).2.2.2
      have htwo := hprime.two_le
      omega
  have hdepth15 : (15, 21) ∈
      paritySafeRechargeExactDepthDualBasePairs 58 := by
    apply mem_paritySafeRechargeExactDepthDualBasePairs.mpr
    refine ⟨mem_paritySafeRechargeExactDualBasePairs.mpr
      ⟨hadmiss15, 3, 5, hwitness15⟩, ?_⟩
    refine ⟨3, 5, hwitness15, ?_⟩
    dsimp [ParitySafeRechargeSelectedDepth]
    left
    norm_num
  have hdepth21 : (21, 15) ∈
      paritySafeRechargeExactDepthDualBasePairs 58 := by
    apply mem_paritySafeRechargeExactDepthDualBasePairs.mpr
    refine ⟨mem_paritySafeRechargeExactDualBasePairs.mpr
      ⟨hadmiss21, 3, 7, hwitness21⟩, ?_⟩
    refine ⟨3, 7, hwitness21, ?_⟩
    dsimp [ParitySafeRechargeSelectedDepth]
    left
    norm_num
  have hseat15 : paritySafeRechargeExactSeat 58 15 21 = 101 := by
    norm_num [paritySafeRechargeExactSeat, paritySafeRechargeExactShellPoint,
      paritySafeRechargeOddShellQuotient]
  have hseat21 : paritySafeRechargeExactSeat 58 21 15 = 101 := by
    norm_num [paritySafeRechargeExactSeat, paritySafeRechargeExactShellPoint,
      paritySafeRechargeOddShellQuotient]
  have hfiber15 : (15, 21) ∈
      paritySafeRechargeExactDepthPairsAtSeat 58 101 :=
    mem_paritySafeRechargeExactDepthPairsAtSeat.mpr ⟨hdepth15, hseat15⟩
  have hfiber21 : (21, 15) ∈
      paritySafeRechargeExactDepthPairsAtSeat 58 101 :=
    mem_paritySafeRechargeExactDepthPairsAtSeat.mpr ⟨hdepth21, hseat21⟩
  have hcard :
      ({(15, 21), (21, 15)} : Finset (ℕ × ℕ)).card ≤
        (paritySafeRechargeExactDepthPairsAtSeat 58 101).card := by
    apply Finset.card_le_card
    intro bt hbt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbt
    rcases hbt with rfl | rfl
    · exact hfiber15
    · exact hfiber21
  norm_num at hcard
  exact ⟨hdepth15, hdepth21, hseat15, hseat21, hcard⟩

end
end DkMath.NumberTheory.Legendre
