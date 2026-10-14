/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity
import DkMath.Combinatorics.FinsetSupportPacking

#print "file: DkMath.NumberTheory.Legendre.CoarseTownSupportPacking"

/-! Actual support collisions, finite deletion packing, and prime-fiber bounds. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.Combinatorics
open scoped BigOperators

/-- Canonically oriented actual old-support collisions, counted once per seat pair. -/
noncomputable def coarseTownSupportCollisionEdges (S : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  supportCollisionEdges (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)

@[simp] theorem mem_coarseTownSupportCollisionEdges {S : Finset ℕ} {n a b : ℕ} :
    (a, b) ∈ coarseTownSupportCollisionEdges S n ↔
      a ∈ coarsePrimeWorldFullTown S n ∧ b ∈ coarsePrimeWorldFullTown S n ∧
      a < b ∧ ¬ Disjoint (squareOffsetPrimeSupport n a) (squareOffsetPrimeSupport n b) :=
  mem_supportCollisionEdges

/-- The neutral deletion lemma yields precisely the family consumed by OldSupportCapacity. -/
theorem exists_coarseTown_supportPacking (S : Finset ℕ) (n : ℕ) :
    ∃ R ⊆ coarsePrimeWorldFullTown S n,
      PairwiseOldSupportDisjointSquareSeatFamily n R ∧
      (coarsePrimeWorldFullTown S n).card ≤ R.card + (coarseTownSupportCollisionEdges S n).card := by
  obtain ⟨R, hR, hfree, hcard⟩ :=
    exists_supportPacking (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)
  refine ⟨R, hR, ⟨?_, hfree⟩, hcard⟩
  intro a ha
  exact mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n (hR ha))

theorem not_fullyCovered_of_coarseTown_edge_deficit (S : Finset ℕ) {n : ℕ}
    (hdef : (primeScalesUpTo n).card + (coarseTownSupportCollisionEdges S n).card <
      (coarsePrimeWorldFullTown S n).card) : ¬ SquareOffsetsFullyCovered n := by
  obtain ⟨R, _hR, hfamily, hcard⟩ := exists_coarseTown_supportPacking S n
  apply not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies hfamily
  omega

/-- A strict edge deficit delegates to the established prime-square-cell consumer. -/
theorem exists_prime_squareCell_of_coarseTown_edge_deficit (S : Finset ℕ) {n : ℕ}
    (hn : 0 < n)
    (hdef : (primeScalesUpTo n).card + (coarseTownSupportCollisionEdges S n).card <
      (coarsePrimeWorldFullTown S n).card) : ∃ p, p.Prime ∧ SquareCell n p := by
  obtain ⟨R, _hR, hfamily, hcard⟩ := exists_coarseTown_supportPacking S n
  apply exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    hn hfamily
  omega

/-- One prime's fiber contributes all its distinct unordered seat pairs. -/
noncomputable def coarseTownPrimeCollisionEdges (S : Finset ℕ) (n q : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((coarseFullTownPrimeFiber S n q).product (coarseFullTownPrimeFiber S n q)).filter
    (fun ab => ab.1 < ab.2)

@[simp] theorem mem_coarseTownPrimeCollisionEdges {S : Finset ℕ} {n q a b : ℕ} :
    (a, b) ∈ coarseTownPrimeCollisionEdges S n q ↔
      a ∈ coarseFullTownPrimeFiber S n q ∧ b ∈ coarseFullTownPrimeFiber S n q ∧ a < b := by
  classical
  simp [coarseTownPrimeCollisionEdges, and_assoc]

theorem card_coarseTownPrimeCollisionEdges (S : Finset ℕ) (n q : ℕ) :
    (coarseTownPrimeCollisionEdges S n q).card = (coarseFullTownPrimeFiber S n q).card.choose 2 := by
  classical
  simpa only [coarseTownPrimeCollisionEdges, Finset.product_eq_sprod] using
    (Finset.card_product_filter_lt (s := coarseFullTownPrimeFiber S n q))

/-- An edge may have several common primes: this is a covering inclusion, not a disjoint union. -/
theorem coarseTownSupportCollisionEdges_subset_prime_union {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownSupportCollisionEdges S n ⊆ (coarseOutsidePrimes S n).biUnion
      (coarseTownPrimeCollisionEdges S n) := by
  classical
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb, hlt, hnd⟩ := mem_coarseTownSupportCollisionEdges.mp hab
  obtain ⟨q, hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
  have hqa := (Finset.mem_inter.mp hq).1
  have hqb := (Finset.mem_inter.mp hq).2
  refine Finset.mem_biUnion.mpr ⟨q,
    coarse_survivor_support_outside (coarseFullTown_survivor hS ha) hqa, ?_⟩
  exact mem_coarseTownPrimeCollisionEdges.mpr
    ⟨Finset.mem_filter.mpr ⟨ha, hqa⟩, Finset.mem_filter.mpr ⟨hb, hqb⟩, hlt⟩

theorem card_coarseTownSupportCollisionEdges_le_fibers {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownSupportCollisionEdges S n).card ≤
      ∑ q ∈ coarseOutsidePrimes S n, (coarseFullTownPrimeFiber S n q).card.choose 2 := by
  classical
  calc
    _ ≤ ((coarseOutsidePrimes S n).biUnion (coarseTownPrimeCollisionEdges S n)).card :=
      Finset.card_le_card (coarseTownSupportCollisionEdges_subset_prime_union hS n)
    _ ≤ ∑ q ∈ coarseOutsidePrimes S n, (coarseTownPrimeCollisionEdges S n q).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [card_coarseTownPrimeCollisionEdges]

/-- Ceiling fiber bounds give a fully explicit, generally coarse collision-edge upper bound. -/
theorem card_coarseTownSupportCollisionEdges_le_ceiling {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownSupportCollisionEdges S n).card ≤
      ∑ q ∈ coarseOutsidePrimes S n,
        ((coarsePrimeWorldBase S n).card * ((coarsePrimeWorldPeriodCount S n + q - 1) / q)).choose 2 := by
  exact (card_coarseTownSupportCollisionEdges_le_fibers hS n).trans
    (Finset.sum_le_sum (fun q hq => Nat.choose_le_choose 2 (card_coarseFullTownPrimeFiber_le hS hq)))

theorem card_coarseTownSupportCollisionEdges_le_uniform {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ}
    (hlarge : ∀ q ∈ coarseOutsidePrimes S n, coarsePrimeWorldPeriodCount S n ≤ q) :
    (coarseTownSupportCollisionEdges S n).card ≤
      (coarseOutsidePrimes S n).card * (coarsePrimeWorldBase S n).card.choose 2 := by
  calc
    _ ≤ ∑ q ∈ coarseOutsidePrimes S n, (coarseFullTownPrimeFiber S n q).card.choose 2 :=
      card_coarseTownSupportCollisionEdges_le_fibers hS n
    _ ≤ ∑ _q ∈ coarseOutsidePrimes S n, (coarsePrimeWorldBase S n).card.choose 2 :=
      Finset.sum_le_sum (fun q hq => Nat.choose_le_choose 2
        (card_coarseFullTownPrimeFiber_le_base hS hq (hlarge q hq)))
    _ = _ := by simp

end DkMath.NumberTheory.Legendre
