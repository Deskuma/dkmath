/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarsePrimorialTown

#print "file: DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown"

/-! Complete-period shell grids, phased columns, and vertical wave capacity. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Certified finite prime worlds always have positive modulus. -/
theorem coarsePrimeWorld_modulus_pos {S : Finset ℕ} (hS : KnownPrimeScales S) :
    0 < primeWorldModulus S :=
  Finset.prod_pos (fun _p hp => (hS hp).pos)

/-- The number of full period blocks; Nat division explicitly returns zero for modulus zero. -/
def coarsePrimeWorldPeriodCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  2 * n / primeWorldModulus S

theorem coarsePeriodCount_zero_modulus {S : Finset ℕ} (hM : primeWorldModulus S = 0)
    (n : ℕ) : coarsePrimeWorldPeriodCount S n = 0 := by
  simp [coarsePrimeWorldPeriodCount, hM]

theorem coarsePeriodCount_mul_le (S : Finset ℕ) (n : ℕ) :
    coarsePrimeWorldPeriodCount S n * primeWorldModulus S ≤ 2 * n :=
  Nat.div_mul_le_self _ _

theorem coarsePeriodCount_succ_mul_gt {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    2 * n < (coarsePrimeWorldPeriodCount S n + 1) * primeWorldModulus S := by
  have hm := Nat.mod_lt (2 * n) (coarsePrimeWorld_modulus_pos hS)
  have he := Nat.mod_add_div (2 * n) (primeWorldModulus S)
  dsimp [coarsePrimeWorldPeriodCount]
  nlinarith

theorem two_le_coarsePeriodCount {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hfit : primeWorldModulus S ≤ n) : 2 ≤ coarsePrimeWorldPeriodCount S n := by
  exact (Nat.le_div_iff_mul_le (coarsePrimeWorld_modulus_pos hS)).mpr (by omega)

/-- Coordinates use the existing phased base and all complete-period indices. -/
def coarsePrimeWorldGridPairs (S : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (coarsePrimeWorldBase S n).product (Finset.range (coarsePrimeWorldPeriodCount S n))

def coarsePrimeWorldGridSeat (S : Finset ℕ) (pair : ℕ × ℕ) : ℕ :=
  pair.1 + pair.2 * primeWorldModulus S

@[simp] theorem mem_coarsePrimeWorldGridPairs {S : Finset ℕ} {n r j : ℕ} :
    (r, j) ∈ coarsePrimeWorldGridPairs S n ↔
      r ∈ coarsePrimeWorldBase S n ∧ j < coarsePrimeWorldPeriodCount S n := by
  simp [coarsePrimeWorldGridPairs]

theorem coarseGridSeat_squareOffset {S : Finset ℕ} {n : ℕ} {pair : ℕ × ℕ}
    (hp : pair ∈ coarsePrimeWorldGridPairs S n) :
    SquareOffset n (coarsePrimeWorldGridSeat S pair) := by
  rcases pair with ⟨r, j⟩
  have h := mem_coarsePrimeWorldGridPairs.mp hp
  have hb := mem_coarsePrimeWorldBase.mp h.1
  have hm := Nat.mul_le_mul_right (primeWorldModulus S) (Nat.succ_le_of_lt h.2)
  have hbound := coarsePeriodCount_mul_le S n
  dsimp [coarsePrimeWorldGridSeat, SquareOffset]
  constructor <;> nlinarith

/-- Shifting representatives by one aligns the endpoint M with the existing reduced-parent API. -/
theorem coarseGridSeat_injective {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    Set.InjOn (coarsePrimeWorldGridSeat S) (coarsePrimeWorldGridPairs S n) := by
  intro a ha b hb he
  rcases a with ⟨r, j⟩
  rcases b with ⟨s, k⟩
  have hr := mem_coarsePrimeWorldBase.mp (mem_coarsePrimeWorldGridPairs.mp ha).1
  have hs := mem_coarsePrimeWorldBase.mp (mem_coarsePrimeWorldGridPairs.mp hb).1
  have he' : primeWorldChild S (r - 1) j = primeWorldChild S (s - 1) k := by
    dsimp [primeWorldChild, coarsePrimeWorldGridSeat] at *
    omega
  have h := (primeWorldChild_eq_iff_of_lt_modulus hS
    (show r - 1 < primeWorldModulus S by omega)
    (show s - 1 < primeWorldModulus S by omega)).mp he'
  have hrs : r = s := by omega
  exact Prod.ext hrs h.2

/-- Only complete blocks are included; the final partial period is omitted. -/
def coarsePrimeWorldFullTown (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (coarsePrimeWorldGridPairs S n).image (coarsePrimeWorldGridSeat S)

@[simp] theorem mem_coarsePrimeWorldFullTown {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarsePrimeWorldFullTown S n ↔
      ∃ r ∈ coarsePrimeWorldBase S n, ∃ j < coarsePrimeWorldPeriodCount S n,
        r + j * primeWorldModulus S = a := by
  simp [coarsePrimeWorldFullTown, Finset.mem_image, Prod.exists,
    coarsePrimeWorldGridSeat, and_assoc]

theorem coarseFullTown_subset_squareOffsets (S : Finset ℕ) (n : ℕ) :
    coarsePrimeWorldFullTown S n ⊆ squareOffsets n := by
  intro a ha
  obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp ha
  exact mem_squareOffsets.mpr (coarseGridSeat_squareOffset hp)

theorem card_coarsePrimeWorldFullTown {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarsePrimeWorldFullTown S n).card =
      coarsePrimeWorldPeriodCount S n * Nat.totient (primeWorldModulus S) := by
  rw [coarsePrimeWorldFullTown, Finset.card_image_iff.mpr (coarseGridSeat_injective hS n)]
  simp [coarsePrimeWorldGridPairs, card_coarsePrimeWorldBase, Nat.mul_comm]

def coarsePrimeWorldColumn (S : Finset ℕ) (n r : ℕ) : Finset ℕ :=
  (Finset.range (coarsePrimeWorldPeriodCount S n)).image (fun j => r + j * primeWorldModulus S)

theorem coarseColumn_subset_fullTown {S : Finset ℕ} {n r : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n) :
    coarsePrimeWorldColumn S n r ⊆ coarsePrimeWorldFullTown S n := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  exact mem_coarsePrimeWorldFullTown.mpr ⟨r, hr, j, Finset.mem_range.mp hj, rfl⟩

theorem card_coarsePrimeWorldColumn {S : Finset ℕ} (hS : KnownPrimeScales S) (n r : ℕ) :
    (coarsePrimeWorldColumn S n r).card = coarsePrimeWorldPeriodCount S n := by
  rw [coarsePrimeWorldColumn, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro j k he
    exact Nat.mul_right_cancel (coarsePrimeWorld_modulus_pos hS) (Nat.add_left_cancel he)

theorem coarseFullTown_eq_column_union (S : Finset ℕ) (n : ℕ) :
    coarsePrimeWorldFullTown S n =
      (coarsePrimeWorldBase S n).biUnion (coarsePrimeWorldColumn S n) := by
  ext a
  simp [mem_coarsePrimeWorldFullTown, coarsePrimeWorldColumn, Finset.mem_image]

theorem disjoint_coarseColumns {S : Finset ℕ} (hS : KnownPrimeScales S) {n r s : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n) (hs : s ∈ coarsePrimeWorldBase S n) (hne : r ≠ s) :
    Disjoint (coarsePrimeWorldColumn S n r) (coarsePrimeWorldColumn S n s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ha
  obtain ⟨k, hk, hf⟩ := Finset.mem_image.mp hb
  have hp := coarseGridSeat_injective hS n
    (mem_coarsePrimeWorldGridPairs.mpr ⟨hr, Finset.mem_range.mp hj⟩)
    (mem_coarsePrimeWorldGridPairs.mpr ⟨hs, Finset.mem_range.mp hk⟩) (he.trans hf.symm)
  exact hne (congrArg Prod.fst hp)

theorem coarseFullTown_address_periodic (S : Finset ℕ) (n r j : ℕ) :
    squareShellWheelProjection S n (r + j * primeWorldModulus S) =
      squareShellWheelProjection S n r := by
  change (n ^ 2 + (r + j * primeWorldModulus S)) % primeWorldModulus S = _
  rw [← Nat.add_assoc]
  simp [squareShellWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct, primeWorldModulus, Nat.add_mod]

theorem coarseFullTown_survivor_periodic (S : Finset ℕ) (n r j : ℕ) :
    SupportDisjointFrom S (n ^ 2 + (r + j * primeWorldModulus S)) ↔
      SupportDisjointFrom S (n ^ 2 + r) := by
  rw [← Nat.add_assoc]
  exact supportDisjointFrom_add_mul_primeWorldModulus_iff

theorem coarseFullTown_survivor {S : Finset ℕ} (hS : KnownPrimeScales S) {n a : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown S n) : SupportDisjointFrom S (n ^ 2 + a) := by
  obtain ⟨r, hr, j, _, rfl⟩ := mem_coarsePrimeWorldFullTown.mp ha
  exact (coarseFullTown_survivor_periodic S n r j).mpr
    (((mem_coarsePrimeWorldBase_iff_survivor hS).mp hr).2.2)

theorem coarseTwoStreet_subset_fullTown {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hfit : primeWorldModulus S ≤ n) :
    coarsePrimeWorldTown S n ⊆ coarsePrimeWorldFullTown S n := by
  intro a ha
  have hK := two_le_coarsePeriodCount hS hfit
  rcases Finset.mem_union.mp ha with hr | hs
  · exact mem_coarsePrimeWorldFullTown.mpr ⟨a, hr, 0, by omega, by simp⟩
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    exact mem_coarsePrimeWorldFullTown.mpr ⟨r, hr, 1, by omega, by simp [Nat.add_comm]⟩

theorem coarseFullTown_eq_twoStreet_of_periodCount_two {S : Finset ℕ} {n : ℕ}
    (hK : coarsePrimeWorldPeriodCount S n = 2) :
    coarsePrimeWorldFullTown S n = coarsePrimeWorldTown S n := by
  ext a
  rw [mem_coarsePrimeWorldFullTown]
  simp only [coarsePrimeWorldTown, coarsePrimeWorldShift, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, j, hj, rfl⟩
    rw [hK] at hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · simp [hr]
    · exact Or.inr ⟨r, hr, by simp [Nat.add_comm]⟩
  · rintro (hr | ⟨r, hr, rfl⟩)
    · exact ⟨a, hr, 0, by omega, by simp⟩
    · exact ⟨r, hr, 1, by omega, by simp [Nat.add_comm]⟩

end DkMath.NumberTheory.Legendre
