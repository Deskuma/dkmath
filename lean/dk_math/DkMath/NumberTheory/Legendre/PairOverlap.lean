/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Wave
import DkMath.NumberTheory.Legendre.Internal.PairCombinatorics

#print "file: DkMath.NumberTheory.Legendre.PairOverlap"

/-!
## PairOverlap

Within-seat unordered pair overlap and near/far product-period ledgers built on the Wave layer.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-- One offset's unordered support-pair multiplicity. -/
noncomputable def squareOffsetPrimePairMultiplicity (n r : ℕ) : ℕ :=
  Nat.choose (squareOffsetPrimeSupport n r).card 2

/-- A support of size `k` has at least `k - 1` unordered distinct pairs. -/
theorem primeSupport_sub_one_le_pairMultiplicity
    {n r : ℕ} :
    (squareOffsetPrimeSupport n r).card - 1 ≤
      squareOffsetPrimePairMultiplicity n r := by
  unfold squareOffsetPrimePairMultiplicity
  rw [Nat.choose_two_right]
  by_cases hsmall : (squareOffsetPrimeSupport n r).card ≤ 1
  · omega
  · have hlarge : 2 ≤ (squareOffsetPrimeSupport n r).card := by omega
    apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right ((squareOffsetPrimeSupport n r).card - 1) hlarge)

/-- One copy of every unordered pair of old prime directions. -/
noncomputable def squarePrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeScalesUpTo n).product (primeScalesUpTo n)).filter
    (fun pair => pair.1 < pair.2)

/-- Membership in the canonical old-prime pair set. -/
@[simp] theorem mem_squarePrimePairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ Nat.Prime q ∧ q ≤ n ∧ p < q := by
  simp [squarePrimePairs, and_assoc, and_left_comm, and_comm]

/-- Pair-overlap incidence count over canonical old-prime pairs. -/
noncomputable def squarePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimePairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The pair ledger is exactly the sum of local unordered support-pair counts. -/
theorem squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ r ∈ squareOffsets n,
        squareOffsetPrimePairMultiplicity n r := by
  classical
  have hpairset (r : ℕ) :
      (squarePrimePairs n).filter
          (fun pair => pair.1 ∈ squareOffsetPrimeSupport n r ∧
            pair.2 ∈ squareOffsetPrimeSupport n r) =
        upperPairs (squareOffsetPrimeSupport n r) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [squarePrimePairs, upperPairs, mem_squareOffsetPrimeSupport,
      and_assoc, and_left_comm, and_comm]
    omega
  unfold squarePrimePairOverlapCount
  calc
    (∑ pair ∈ squarePrimePairs n,
        (squarePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squarePrimePairs n, ∑ r ∈ squareOffsets n,
          if SquareOffsetForbiddenBy n pair.1 r ∧
              SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      simp [squarePrimePairOverlapOffsets, squareOffsets]
    _ = ∑ r ∈ squareOffsets n, ∑ pair ∈ squarePrimePairs n,
          if SquareOffsetForbiddenBy n pair.1 r ∧
              SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareOffsets n,
          ((squarePrimePairs n).filter
            (fun pair => pair.1 ∈ squareOffsetPrimeSupport n r ∧
              pair.2 ∈ squareOffsetPrimeSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext pair
      rcases pair with ⟨p, q⟩
      have hfilter :
          (squarePrimePairs n).filter
              (fun pair => SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 r) =
            (squarePrimePairs n).filter
              (fun pair => pair.1 ∈ squareOffsetPrimeSupport n r ∧
                pair.2 ∈ squareOffsetPrimeSupport n r) := by
        ext pair
        simp only [Finset.mem_filter]
        rw [mem_squareOffsetPrimeSupport, mem_squareOffsetPrimeSupport]
        constructor
        · rintro ⟨hmem, h₁, h₂⟩
          rcases mem_squarePrimePairs.mp hmem with
            ⟨hp, hpn, hq, hqn, hpq⟩
          exact ⟨hmem, ⟨hp, hpn, h₁⟩, hq, hqn, h₂⟩
        · rintro ⟨hmem, ⟨hp, hpn, h₁⟩, hq, hqn, h₂⟩
          exact ⟨hmem, h₁, h₂⟩
      exact (congrArg (fun S => (p, q) ∈ S) hfilter).to_iff
    _ = ∑ r ∈ squareOffsets n,
          (upperPairs (squareOffsetPrimeSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hpairset]
    _ = ∑ r ∈ squareOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold squareOffsetPrimePairMultiplicity
      exact card_upperPairs_eq_choose _

/-- Pair multiplicity dominates the repeated-support excess at every offset. -/
theorem squareCoverOverlapExcess_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareCoverOverlapExcess n ≤ squarePrimePairOverlapCount n := by
  rw [squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity]
  unfold squareCoverOverlapExcess
  apply Finset.sum_le_sum
  intro r hr
  exact primeSupport_sub_one_le_pairMultiplicity

/-- Full cover obeys the second-order pair-overlap budget constraint. -/
theorem baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n + squarePrimePairOverlapCount n := by
  calc
    squareCoverBaselineIncidence n + squareAnchorCarryCount n =
        2 * n + squareCoverOverlapExcess n :=
      squareCoverBaselineIncidence_add_squareAnchorCarryCount_eq_two_mul_add_overlapExcess_of_fullyCovered
        hfull
    _ ≤ 2 * n + squarePrimePairOverlapCount n := by
      exact Nat.add_le_add_left
        (squareCoverOverlapExcess_le_squarePrimePairOverlapCount n) (2 * n)

/-- Pair overlap reduces to exact occupancy of the product-modulus wave. -/
theorem squarePrimePairOverlapCount_eq_sum_product_div_add_carry
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ pair ∈ squarePrimePairs n,
        ((2 * n) / (pair.1 * pair.2) +
          squareWaveCarry n (pair.1 * pair.2)) := by
  unfold squarePrimePairOverlapCount
  apply Finset.sum_congr rfl
  intro pair hpair
  rcases pair with ⟨p, q⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq⟩
  simpa using
    (show (squarePrimePairOverlapOffsets n p q).card =
        (2 * n) / (p * q) + squareWaveCarry n (p * q) by
      rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq
        hpq.ne]
      exact card_squareWaveOffsets_eq_div_add_carry
        (Nat.mul_pos hp.pos hq.pos))

/-- The full-cover pair budget in its expanded product-wave arithmetic form. -/
theorem baseline_add_carry_le_two_mul_add_sum_product_div_add_carry_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n +
        ∑ pair ∈ squarePrimePairs n,
          ((2 * n) / (pair.1 * pair.2) +
            squareWaveCarry n (pair.1 * pair.2)) := by
  rw [← squarePrimePairOverlapCount_eq_sum_product_div_add_carry]
  exact baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered hfull

/-!
### PRIM-L010: near/far pair localization

The second-order pair ledger is now localized by the product modulus relative
to the actual square-window length `2 * n`.  Near products retain a complete
period baseline, while far products have no complete period and can contribute
only their one-bit square-anchor carry.  This is finite localization, not an
analytic estimate or a claim of independence between prime directions.
-/

/-- Canonical old-prime pairs whose product period fits in the square window. -/
noncomputable def squarePrimeNearPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => pair.1 * pair.2 ≤ 2 * n)

/-- Canonical old-prime pairs whose product period exceeds the square window. -/
noncomputable def squarePrimeFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => 2 * n < pair.1 * pair.2)

/-- Membership in the near canonical pair set. -/
@[simp] theorem mem_squarePrimeNearPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeNearPairs n ↔
      (p, q) ∈ squarePrimePairs n ∧ p * q ≤ 2 * n := by
  simp [squarePrimeNearPairs]

/-- Membership in the far canonical pair set. -/
@[simp] theorem mem_squarePrimeFarPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeFarPairs n ↔
      (p, q) ∈ squarePrimePairs n ∧ 2 * n < p * q := by
  simp [squarePrimeFarPairs]

/-- The near and far pair sets form an exact disjoint partition. -/
theorem squarePrimeNearPairs_union_farPairs (n : ℕ) :
    squarePrimeNearPairs n ∪ squarePrimeFarPairs n = squarePrimePairs n := by
  ext pair
  rcases pair with ⟨p, q⟩
  by_cases hnear : p * q ≤ 2 * n
  · simp [squarePrimeNearPairs, squarePrimeFarPairs, hnear]
  · have hfar : 2 * n < p * q := lt_of_not_ge hnear
    simp [squarePrimeNearPairs, squarePrimeFarPairs, hnear, hfar]

/-- Near and far canonical pairs are disjoint. -/
theorem disjoint_squarePrimeNearPairs_squarePrimeFarPairs (n : ℕ) :
    Disjoint (squarePrimeNearPairs n) (squarePrimeFarPairs n) := by
  rw [Finset.disjoint_left]
  intro pair hnear hfar
  have hnear' := mem_squarePrimeNearPairs.mp hnear
  have hfar' := mem_squarePrimeFarPairs.mp hfar
  omega

/-- The near-pair contribution to the second-order overlap ledger. -/
noncomputable def squarePrimeNearPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The far-pair contribution to the second-order overlap ledger. -/
noncomputable def squarePrimeFarPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeFarPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The total pair ledger splits exactly into near and far contributions. -/
theorem squarePrimePairOverlapCount_eq_near_add_far
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairOverlapCount n +
        squarePrimeFarPairOverlapCount n := by
  unfold squarePrimePairOverlapCount squarePrimeNearPairOverlapCount
    squarePrimeFarPairOverlapCount
  rw [show squarePrimePairs n =
      squarePrimeNearPairs n ∪ squarePrimeFarPairs n by
        symm
        exact squarePrimeNearPairs_union_farPairs n]
  rw [Finset.sum_union (disjoint_squarePrimeNearPairs_squarePrimeFarPairs n)]

/-- A wave longer than the window has occupancy equal to its anchor carry. -/
theorem card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus
    {n m : ℕ}
    (hm : 0 < m)
    (hfar : 2 * n < m) :
    (squareWaveOffsets n m).card = squareWaveCarry n m := by
  rw [card_squareWaveOffsets_eq_div_add_carry hm,
    Nat.div_eq_of_lt hfar, Nat.zero_add]

/-- A far canonical prime pair has overlap occupancy equal to its product carry. -/
theorem card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far
    {n p q : ℕ}
    (hpq : (p, q) ∈ squarePrimeFarPairs n) :
    (squarePrimePairOverlapOffsets n p q).card =
      squareWaveCarry n (p * q) := by
  rcases mem_squarePrimeFarPairs.mp hpq with ⟨hpair, hfar⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq'⟩
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq'.ne]
  exact card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus
    (Nat.mul_pos hp.pos hq.pos) hfar

/-- Far pairs whose product wave actually hits the square window. -/
noncomputable def squarePrimeActiveFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimeFarPairs n).filter
    (fun pair => squareWaveCarry n (pair.1 * pair.2) = 1)

/-- Membership in the active far-pair set. -/
@[simp] theorem mem_squarePrimeActiveFarPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeActiveFarPairs n ↔
      (p, q) ∈ squarePrimeFarPairs n ∧
        squareWaveCarry n (p * q) = 1 := by
  simp [squarePrimeActiveFarPairs]

/-- The far overlap ledger is exactly the number of active far pairs. -/
theorem squarePrimeFarPairOverlapCount_eq_card_activeFarPairs
    (n : ℕ) :
    squarePrimeFarPairOverlapCount n =
      (squarePrimeActiveFarPairs n).card := by
  unfold squarePrimeFarPairOverlapCount
  calc
    (∑ pair ∈ squarePrimeFarPairs n,
        (squarePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squarePrimeFarPairs n,
          squareWaveCarry n (pair.1 * pair.2) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far hpair
    _ = ∑ pair ∈ squarePrimeFarPairs n,
          if squareWaveCarry n (pair.1 * pair.2) = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hmem := mem_squarePrimeFarPairs.mp hpair
      rcases mem_squarePrimePairs.mp hmem.1 with ⟨hp, hpn, hq, hqn, hpq⟩
      have hle := squareWaveCarry_le_one (n := n)
        (m := pair.1 * pair.2) (Nat.mul_pos hp.pos hq.pos)
      split_ifs with hcarry
      · simp [hcarry]
      · have hzero : squareWaveCarry n (pair.1 * pair.2) = 0 := by
          omega
        simp [hzero]
    _ = (squarePrimeActiveFarPairs n).card := by
      rw [Finset.sum_boole]
      rfl

/-- A far pair is active exactly when its product wave is nonempty. -/
theorem mem_squarePrimeActiveFarPairs_iff_overlap_nonempty
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeActiveFarPairs n ↔
      (p, q) ∈ squarePrimeFarPairs n ∧
        (squarePrimePairOverlapOffsets n p q).Nonempty := by
  constructor
  · intro hactive
    refine ⟨(mem_squarePrimeActiveFarPairs.mp hactive).1, ?_⟩
    apply Finset.card_pos.mp
    rw [card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far
      (mem_squarePrimeActiveFarPairs.mp hactive).1]
    exact (mem_squarePrimeActiveFarPairs.mp hactive).2 ▸ Nat.zero_lt_one
  · rintro ⟨hfar, hnonempty⟩
    rw [mem_squarePrimeActiveFarPairs]
    refine ⟨hfar, ?_⟩
    have hpos := Finset.card_pos.mpr hnonempty
    have hcard := card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far hfar
    have hpair := mem_squarePrimeFarPairs.mp hfar
    rcases mem_squarePrimePairs.mp hpair.1 with ⟨hp, hpn, hq, hqn, hpq⟩
    have hle := squareWaveCarry_le_one (n := n)
      (m := p * q) (Nat.mul_pos hp.pos hq.pos)
    omega

/-- The complete product-period baseline contributed by near pairs. -/
noncomputable def squarePrimeNearPairBaseline (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (2 * n) / (pair.1 * pair.2)

/-- The product-wave carry count contributed by near pairs. -/
noncomputable def squarePrimeNearPairCarryCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    squareWaveCarry n (pair.1 * pair.2)

/-- Near-pair overlap is exactly baseline periods plus product carries. -/
theorem squarePrimeNearPairOverlapCount_eq_baseline_add_carry
    (n : ℕ) :
    squarePrimeNearPairOverlapCount n =
      squarePrimeNearPairBaseline n + squarePrimeNearPairCarryCount n := by
  unfold squarePrimeNearPairOverlapCount squarePrimeNearPairBaseline
    squarePrimeNearPairCarryCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair hpair
  rcases pair with ⟨p, q⟩
  rcases mem_squarePrimeNearPairs.mp hpair with ⟨hprimepair, hnear⟩
  rcases mem_squarePrimePairs.mp hprimepair with ⟨hp, hpn, hq, hqn, hpq⟩
  simpa using
    (show (squarePrimePairOverlapOffsets n p q).card =
        (2 * n) / (p * q) + squareWaveCarry n (p * q) by
      rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq
        hpq.ne]
      exact card_squareWaveOffsets_eq_div_add_carry
        (Nat.mul_pos hp.pos hq.pos))

/-- Every near pair contributes at least one product-wave overlap seat. -/
theorem one_le_card_squarePrimePairOverlapOffsets_of_mem_near
    {n p q : ℕ}
    (hpq : (p, q) ∈ squarePrimeNearPairs n) :
    1 ≤ (squarePrimePairOverlapOffsets n p q).card := by
  rcases mem_squarePrimeNearPairs.mp hpq with ⟨hpair, hnear⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq'⟩
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq'.ne,
    card_squareWaveOffsets_eq_div_add_carry (Nat.mul_pos hp.pos hq.pos)]
  have hdiv : 1 ≤ (2 * n) / (p * q) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hq.pos)).2
    simpa using hnear
  omega

/-- The complete pair ledger has near baseline, near carry, and active far parts. -/
theorem squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairBaseline n +
        squarePrimeNearPairCarryCount n +
          (squarePrimeActiveFarPairs n).card := by
  rw [squarePrimePairOverlapCount_eq_near_add_far,
    squarePrimeNearPairOverlapCount_eq_baseline_add_carry,
    squarePrimeFarPairOverlapCount_eq_card_activeFarPairs]

/-- Full cover in the localized near/far second-order normal form. -/
theorem baseline_add_carry_le_two_mul_add_near_far_pair_budget_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n +
        (squarePrimeNearPairBaseline n +
          squarePrimeNearPairCarryCount n +
            (squarePrimeActiveFarPairs n).card) := by
  calc
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
        2 * n + squarePrimePairOverlapCount n :=
      baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered hfull
    _ = 2 * n +
        (squarePrimeNearPairBaseline n +
          squarePrimeNearPairCarryCount n +
            (squarePrimeActiveFarPairs n).card) := by
      rw [squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar]


end DkMath.NumberTheory.Legendre
