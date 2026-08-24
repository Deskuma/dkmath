/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.Obstruction
import DkMath.NumberTheory.Legendre.Internal.PairCombinatorics

open DkMath.NumberTheory.Legendre.Internal
#print "file: DkMath.NumberTheory.Legendre.LocalizedObstruction"

/-!
## LocalizedObstruction

PRIM-L018 coprime-local depth and within-seat pair ledgers.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-!
### PRIM-L018: coprime-local obstruction ledgers

PRIM-L017 classifies coprime covered seats, but charges its depth and pair
obstructions to ledgers over the whole square window.  This checkpoint keeps
the same seat classification while restricting both ledgers to coprime seats
and to the anchor-nondivisor prime world.  The resulting identities are
finite incidence statements: local depth counts distinct prime-square
divisibility witnesses, not p-adic valuation mass, and the pair ledger counts
unordered distinct nondivisor-prime pairs.  The localized budgets are proved
to be no larger than their PRIM-L017 predecessors.  No contradiction, simple
seat existence, or Legendre theorem is asserted here.
-/

/-! ### PRIM-L018.1: local prime-square waves and depth -/

/-- Coprime seats hit by the square wave of one nondivisor prime. -/
noncomputable def squareAnchorCoprimePrimeSquareOffsets
    (n p : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => p ^ 2 ∣ n ^ 2 + r)

@[simp] theorem mem_squareAnchorCoprimePrimeSquareOffsets
    {n p r : ℕ} :
    r ∈ squareAnchorCoprimePrimeSquareOffsets n p ↔
      r ∈ squareAnchorCoprimeOffsets n ∧ p ^ 2 ∣ n ^ 2 + r := by
  simp [squareAnchorCoprimePrimeSquareOffsets]

/-- The coprime-local wave is contained in the existing square wave. -/
theorem squareAnchorCoprimePrimeSquareOffsets_subset_squareWaveOffsets
    (n p : ℕ) :
    squareAnchorCoprimePrimeSquareOffsets n p ⊆
      squareWaveOffsets n (p ^ 2) := by
  intro r hr
  have hr' := mem_squareAnchorCoprimePrimeSquareOffsets.mp hr
  exact mem_squareWaveOffsets.mpr
    ⟨(mem_squareAnchorCoprimeOffsets.mp hr'.1).1, hr'.2⟩

/-- The depth ledger restricted to coprime seats and nondivisor directions.

This is an upper ledger: a multi-support seat is counted whenever one of its
nondivisor directions has a prime-square hit. -/
noncomputable def squareAnchorCoprimePrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareAnchorCoprimePrimeSquareOffsets n p).card

/-- Singleton-depth seats are paid for by the coprime-local depth ledger. -/
theorem card_singletonDepthOffsets_le_coprimePrimeSquareDepthBudget
    (n : ℕ) :
    (squareAnchorCoprimeSingletonDepthOffsets n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
  have hsubset : squareAnchorCoprimeSingletonDepthOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr).1
  calc
    (squareAnchorCoprimeSingletonDepthOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr
      rcases hr'.2 with ⟨p, hp, _, hdepth⟩
      have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
      have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
        mem_squareAnchorNondivisorPrimes.mpr
          ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
      have hlocal : r ∈ squareAnchorCoprimePrimeSquareOffsets n p :=
        mem_squareAnchorCoprimePrimeSquareOffsets.mpr ⟨hr'.1, hdepth⟩
      have hsingle := Finset.single_le_sum
        (f := fun q =>
          if r ∈ squareAnchorCoprimePrimeSquareOffsets n q then 1 else 0)
        (fun q _ => Nat.zero_le _) hpWorld
      simpa [hlocal] using hsingle
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          (squareAnchorCoprimePrimeSquareOffsets n p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareAnchorCoprimePrimeSquareOffsets]

/-- The localized depth ledger is bounded by the PRIM-L017 global ledger. -/
theorem squareAnchorCoprimePrimeSquareDepthBudget_le_primeSquareDepthBudget
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n ≤
      squareAnchorPrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
    squareAnchorPrimeSquareDepthBudget
  apply Finset.sum_le_sum
  intro p hp
  exact Finset.card_le_card
    (squareAnchorCoprimePrimeSquareOffsets_subset_squareWaveOffsets n p)

/-- Number of distinct nondivisor prime-square witnesses at one coprime seat. -/
noncomputable def squareAnchorCoprimeDepthMultiplicity
    (n r : ℕ) : ℕ := by
  classical
  exact ((squareAnchorNondivisorPrimes n).filter
    (fun p => p ^ 2 ∣ n ^ 2 + r)).card

/-- Exact transpose of the localized prime-square incidence ledger. -/
theorem squareAnchorCoprimePrimeSquareDepthBudget_eq_sum_local_depthMultiplicity
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        squareAnchorCoprimeDepthMultiplicity n r := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
  calc
    (∑ p ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimePrimeSquareOffsets n p).card) =
        ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareAnchorCoprimePrimeSquareOffsets]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareAnchorCoprimeDepthMultiplicity n r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [show (squareAnchorCoprimeDepthMultiplicity n r) =
        ((squareAnchorNondivisorPrimes n).filter
          (fun p => p ^ 2 ∣ n ^ 2 + r)).card by
            rfl]
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext p
      simp [squareAnchorCoprimePrimeSquareOffsets, hr]

/-! ### PRIM-L018.2: local nondivisor-prime pairs -/

/-- One canonical copy of every unordered pair of anchor-nondivisor primes. -/
noncomputable def squareAnchorNondivisorPrimePairs (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorNondivisorPrimes n)).filter
      (fun pair => pair.1 < pair.2)

/-- Membership in the canonical local nondivisor-prime pair set. -/
@[simp] theorem mem_squareAnchorNondivisorPrimePairs
    {n p q : ℕ} :
    (p, q) ∈ squareAnchorNondivisorPrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
        Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ p < q := by
  simp [squareAnchorNondivisorPrimePairs, and_assoc, and_left_comm,
    and_comm]

/-- The local canonical pair set is contained in the global old-prime pairs. -/
theorem squareAnchorNondivisorPrimePairs_subset_squarePrimePairs
    (n : ℕ) :
    squareAnchorNondivisorPrimePairs n ⊆ squarePrimePairs n := by
  intro pair hp
  rcases pair with ⟨p, q⟩
  have hpq : p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧ p < q := by
    have hp' : (p, q) ∈
        ((squareAnchorNondivisorPrimes n).product
          (squareAnchorNondivisorPrimes n)).filter
            (fun pair => pair.1 < pair.2) := by
      simpa [squareAnchorNondivisorPrimePairs] using hp
    have hfilter := Finset.mem_filter.mp hp'
    have hprod := Finset.mem_product.mp hfilter.1
    exact ⟨hprod.1, hprod.2, hfilter.2⟩
  have hp' := mem_squareAnchorNondivisorPrimes.mp hpq.1
  have hq' := mem_squareAnchorNondivisorPrimes.mp hpq.2.1
  exact mem_squarePrimePairs.mpr
    ⟨hp'.1, hp'.2.1, hq'.1, hq'.2.1, hpq.2.2⟩

/-- Coprime seats carrying one specified nondivisor-prime pair. -/
noncomputable def squareAnchorCoprimePrimePairOverlapOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r =>
      SquareOffsetForbiddenBy n p r ∧
        SquareOffsetForbiddenBy n q r)

@[simp] theorem mem_squareAnchorCoprimePrimePairOverlapOffsets
    {n p q r : ℕ} :
    r ∈ squareAnchorCoprimePrimePairOverlapOffsets n p q ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareOffsetForbiddenBy n p r ∧
          SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimePrimePairOverlapOffsets, and_assoc]

/-- The localized unordered-pair incidence ledger. -/
noncomputable def squareAnchorCoprimePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
    (squareAnchorCoprimePrimePairOverlapOffsets n pair.1 pair.2).card

/-- Exact local pair double count using the same support as the seat trichotomy. -/
theorem squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
  classical
  have hpairset (r : ℕ) :
      (squareAnchorNondivisorPrimePairs n).filter
          (fun pair =>
            pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
              pair.2 ∈ squareOffsetAnchorNondivisorSupport n r) =
        upperPairs (squareOffsetAnchorNondivisorSupport n r) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [squareAnchorNondivisorPrimePairs, upperPairs,
      mem_squareOffsetAnchorNondivisorSupport, and_assoc,
      and_left_comm, and_comm]
    omega
  unfold squareAnchorCoprimePrimePairOverlapCount
  calc
    (∑ pair ∈ squareAnchorNondivisorPrimePairs n,
        (squareAnchorCoprimePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      simp [squareAnchorCoprimePrimePairOverlapOffsets]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ((squareAnchorNondivisorPrimePairs n).filter
            (fun pair =>
              pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
                pair.2 ∈ squareOffsetAnchorNondivisorSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext pair
      rcases pair with ⟨p, q⟩
      simp [mem_squareOffsetAnchorNondivisorSupport,
        SquareOffsetForbiddenBy]
      aesop
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          (upperPairs (squareOffsetAnchorNondivisorSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hpairset]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact card_upperPairs_eq_choose _

/-! ### PRIM-L018.3: localized budgets and seat certificate -/

/- A support of size at least two contributes at least one unordered pair. -/
private theorem one_le_choose_two_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ Nat.choose k 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
  have hk' : 1 ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul hk hk'
  simpa [Nat.mul_comm] using hmul

/-- Multi-support seats are paid for by the localized pair ledger. -/
theorem card_multiSupportOffsets_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squareAnchorCoprimePrimePairOverlapCount n := by
  classical
  have hmulti_subset : squareAnchorCoprimeMultiSupportOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hr).1
  calc
    (squareAnchorCoprimeMultiSupportOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hmulti := mem_squareAnchorCoprimeMultiSupportOffsets.mp hr
      exact one_le_choose_two_of_two_le hmulti.2
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hmulti_subset
        (fun r _ _ => Nat.zero_le _)
    _ = squareAnchorCoprimePrimePairOverlapCount n :=
      (squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support n).symm

/-- The localized pair ledger is bounded by the PRIM-L009 global pair ledger. -/
theorem squareAnchorCoprimePrimePairOverlapCount_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n ≤
      squarePrimePairOverlapCount n := by
  classical
  have hsubset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp hr).1
  have hpointwise :
      (∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2) =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        squareOffsetPrimePairMultiplicity n r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hcop := mem_squareAnchorCoprimeOffsets.mp hr
    have hnpos : 0 < n := by
      dsimp [SquareOffset] at hcop
      omega
    unfold squareOffsetPrimePairMultiplicity
    rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
      hnpos hcop.2]
  calc
    squareAnchorCoprimePrimePairOverlapCount n =
        ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 :=
      squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support n
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareOffsetPrimePairMultiplicity n r := hpointwise
    _ ≤ ∑ r ∈ squareOffsets n, squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = squarePrimePairOverlapCount n :=
      (squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity n).symm

/-- A covered coprime non-simple seat pays one unit to a local obstruction. -/
theorem one_le_depthMultiplicity_add_pairMultiplicity_of_coprime_covered_not_simple
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r)
    (hnotSimple : ¬ SquareAnchorCoprimeSimpleFreshSeat n r) :
    1 ≤ squareAnchorCoprimeDepthMultiplicity n r +
      Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
  rcases coprime_covered_seat_trichotomy hn hr hcovered with
    hsimple | hdepth | hmulti
  · exact False.elim (hnotSimple hsimple)
  · rcases hdepth with ⟨p, hp, _, hdepth⟩
    have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
    have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
      mem_squareAnchorNondivisorPrimes.mpr
        ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
    have hpDepth : p ∈ (squareAnchorNondivisorPrimes n).filter
        (fun q => q ^ 2 ∣ n ^ 2 + r) :=
      Finset.mem_filter.mpr ⟨hpWorld, hdepth⟩
    have hpos : 0 < squareAnchorCoprimeDepthMultiplicity n r := by
      dsimp [squareAnchorCoprimeDepthMultiplicity]
      exact Finset.card_pos.mpr ⟨p, hpDepth⟩
    omega
  · have hchoose := one_le_choose_two_of_two_le hmulti
    omega

/-! ### PRIM-L018.4: the localized full-cover frontier -/

/-- Full cover is charged to simple seats and the two coprime-local ledgers. -/
theorem two_mul_totient_le_simpleFresh_add_localDepth_add_localPair_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n := by
  have hpartition :=
    two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered hn hfull
  have hdepth :=
    card_singletonDepthOffsets_le_coprimePrimeSquareDepthBudget n
  have hmulti := card_multiSupportOffsets_le_coprimePrimePairOverlapCount n
  calc
    2 * Nat.totient n =
        (squareAnchorCoprimeSimpleFreshOffsets n).card +
          (squareAnchorCoprimeSingletonDepthOffsets n).card +
          (squareAnchorCoprimeMultiSupportOffsets n).card := hpartition
    _ ≤ (squareAnchorCoprimeSimpleFreshOffsets n).card +
          squareAnchorCoprimePrimeSquareDepthBudget n +
          squareAnchorCoprimePrimePairOverlapCount n := by omega

/-- If no simple seat exists, only the localized obstruction ledgers remain. -/
theorem two_mul_totient_le_localDepth_add_localPair_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n := by
  have hmain :=
    two_mul_totient_le_simpleFresh_add_localDepth_add_localPair_of_fullyCovered
      hn hfull
  simpa [hno] using hmain

/-- The localized obstruction capacity is no larger than PRIM-L017's capacity.

This explicit domination records that PRIM-L018 removes bookkeeping waste
rather than merely renaming the earlier frontier. -/
theorem squareAnchorCoprimeLocalDepth_add_pairOverlap_le_globalDepth_add_pairOverlap
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n +
        squareAnchorCoprimePrimePairOverlapCount n ≤
      squareAnchorPrimeSquareDepthBudget n +
        squarePrimePairOverlapCount n := by
  have hdepth :=
    squareAnchorCoprimePrimeSquareDepthBudget_le_primeSquareDepthBudget n
  have hpair :=
    squareAnchorCoprimePrimePairOverlapCount_le_squarePrimePairOverlapCount n
  omega

end DkMath.NumberTheory.Legendre

