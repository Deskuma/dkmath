/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PrimeWorldPacketBridge

#print "file: DkMath.NumberTheory.Legendre.CoarsePrimorialTown"

/-! Finite phased streets and exact outside-prime assignment constraints. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- The second street is one certified world period to the right. -/
def coarsePrimeWorldShift (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (coarsePrimeWorldBase S n).image (fun r => primeWorldModulus S + r)

/-- The two streets inside a single square shell. -/
def coarsePrimeWorldTown (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  coarsePrimeWorldBase S n ∪ coarsePrimeWorldShift S n

theorem coarsePrimeWorldBase_squareOffsets {S : Finset ℕ} {n r : ℕ}
    (hfit : primeWorldModulus S ≤ n) (hr : r ∈ coarsePrimeWorldBase S n) :
    SquareOffset n r ∧ SquareOffset n (primeWorldModulus S + r) := by
  have hb := mem_coarsePrimeWorldBase.mp hr
  constructor <;> constructor <;> omega

theorem disjoint_coarsePrimeWorldStreets (S : Finset ℕ) (n : ℕ) :
    Disjoint (coarsePrimeWorldBase S n) (coarsePrimeWorldShift S n) := by
  rw [Finset.disjoint_left]
  intro r hr hs
  obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hs
  have hr' := mem_coarsePrimeWorldBase.mp hr
  have hs' := mem_coarsePrimeWorldBase.mp hs
  omega

theorem card_coarsePrimeWorldShift (S : Finset ℕ) (n : ℕ) :
    (coarsePrimeWorldShift S n).card = (coarsePrimeWorldBase S n).card := by
  unfold coarsePrimeWorldShift
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)

theorem card_coarsePrimeWorldTown (S : Finset ℕ) (n : ℕ) :
    (coarsePrimeWorldTown S n).card = 2 * Nat.totient (primeWorldModulus S) := by
  rw [coarsePrimeWorldTown, Finset.card_union_of_disjoint
    (disjoint_coarsePrimeWorldStreets S n), card_coarsePrimeWorldShift,
    card_coarsePrimeWorldBase]
  omega

theorem coarsePrimeWorldTown_squareOffsets {S : Finset ℕ} {n r : ℕ}
    (hfit : primeWorldModulus S ≤ n) (hr : r ∈ coarsePrimeWorldTown S n) :
    SquareOffset n r := by
  rcases Finset.mem_union.mp hr with hb | hs
  · exact (coarsePrimeWorldBase_squareOffsets hfit hb).1
  · obtain ⟨s, hb, rfl⟩ := Finset.mem_image.mp hs
    exact (coarsePrimeWorldBase_squareOffsets hfit hb).2

/-- The two complete points have the same phased residue. -/
theorem coarsePrimeWorld_address_shift (S : Finset ℕ) (n r : ℕ) :
    squareShellWheelProjection S n (primeWorldModulus S + r) =
      squareShellWheelProjection S n r := by
  change (n ^ 2 + (primeWorldModulus S + r)) % primeWorldModulus S = _
  rw [show n ^ 2 + (primeWorldModulus S + r) =
    (n ^ 2 + r) + primeWorldModulus S by omega]
  exact Nat.add_mod_right _ _

theorem coarsePrimeWorld_survivor_shift {S : Finset ℕ} {n r : ℕ} :
    SupportDisjointFrom S (n ^ 2 + (primeWorldModulus S + r)) ↔
      SupportDisjointFrom S (n ^ 2 + r) := by
  rw [show n ^ 2 + (primeWorldModulus S + r) =
    (n ^ 2 + r) + primeWorldModulus S by omega]
  exact supportDisjointFrom_add_primeWorldModulus_iff

/-- Euclidean coprimality holds for every base packet, without any anchor divisibility premise. -/
theorem coprime_coarsePrimeWorldPoints {S : Finset ℕ} {n r : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n) :
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + (primeWorldModulus S + r)) := by
  have hc := (mem_coarsePrimeWorldBase.mp hr).2.2
  rw [show n ^ 2 + (primeWorldModulus S + r) =
    (n ^ 2 + r) + primeWorldModulus S by omega, Nat.coprime_self_add_right]
  exact hc

theorem not_prime_dvd_both_coarsePoints {S : Finset ℕ} {n r p : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n) (hp : Nat.Prime p) :
    ¬ (p ∣ n ^ 2 + r ∧ p ∣ n ^ 2 + (primeWorldModulus S + r)) := by
  intro h
  exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt h.1 h.2)
    (coprime_coarsePrimeWorldPoints hr)

theorem coprime_coarsePoint_factors {S : Finset ℕ} {n r a b : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n)
    (ha : a ∣ n ^ 2 + r) (hb : b ∣ n ^ 2 + (primeWorldModulus S + r)) :
    Nat.Coprime a b :=
  Nat.Coprime.of_dvd ha hb (coprime_coarsePrimeWorldPoints hr)

/-- Remaining bounded directions, after removing the selected finite world. -/
def coarseOutsidePrimes (S : Finset ℕ) (n : ℕ) : Finset ℕ := primeScalesUpTo n \ S

theorem coarse_survivor_support_outside {S : Finset ℕ} {n r : ℕ}
    (hdisj : SupportDisjointFrom S (n ^ 2 + r)) :
    squareOffsetPrimeSupport n r ⊆ coarseOutsidePrimes S n := by
  intro p hp
  have hp' := mem_squareOffsetPrimeSupport.mp hp
  exact Finset.mem_sdiff.mpr ⟨mem_primeScalesUpTo.mpr ⟨hp'.1, hp'.2.1⟩,
    hdisj hp'.1 hp'.2.2⟩

theorem prime_outside_not_dvd_coarseModulus {S : Finset ℕ}
    (hS : KnownPrimeScales S) {p : ℕ} (hp : Nat.Prime p) (hpS : p ∉ S) :
    ¬ p ∣ primeWorldModulus S := by
  intro hd
  obtain ⟨q, hq, hpq⟩ := hp.prime.dvd_finsetProd_iff id |>.mp hd
  have he : p = q := (Nat.dvd_prime (hS hq)).mp hpq |>.resolve_left hp.ne_one
  exact hpS (he ▸ hq)

/-- Every fully covered coarse packet supplies two distinct outside assignments. -/
theorem exists_distinct_coarseOutside_cover_pair {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n r : ℕ} (hfit : primeWorldModulus S ≤ n)
    (hr : r ∈ coarsePrimeWorldBase S n) (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q, p ∈ coarseOutsidePrimes S n ∧ q ∈ coarseOutsidePrimes S n ∧ p ≠ q ∧
      p ∈ squareOffsetPrimeSupport n r ∧
      q ∈ squareOffsetPrimeSupport n (primeWorldModulus S + r) := by
  have hseats := coarsePrimeWorldBase_squareOffsets hfit hr
  obtain ⟨p, hp⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp (hfull r hseats.1)
  obtain ⟨q, hq⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hseats.2)
  have hdisj := ((mem_coarsePrimeWorldBase_iff_survivor hS).mp hr).2.2
  refine ⟨p, q, coarse_survivor_support_outside hdisj hp,
    coarse_survivor_support_outside (coarsePrimeWorld_survivor_shift.mpr hdisj) hq, ?_, hp, hq⟩
  intro he
  subst q
  exact not_prime_dvd_both_coarsePoints hr (mem_squareOffsetPrimeSupport.mp hp).1
    ⟨(mem_squareOffsetPrimeSupport.mp hp).2.2, (mem_squareOffsetPrimeSupport.mp hq).2.2⟩

/-- All available ordered outside directions, including unused ones. -/
def coarseOutsideOrderedPairs (S : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((coarseOutsidePrimes S n).product (coarseOutsidePrimes S n)).filter
    (fun pq => pq.1 ≠ pq.2)

/-- The actual incidence fiber of one ordered direction pair. -/
noncomputable def coarseCrossOffsets (S : Finset ℕ) (n p q : ℕ) : Finset ℕ :=
  (coarsePrimeWorldBase S n).filter
    (fun r => p ∈ squareOffsetPrimeSupport n r ∧
      q ∈ squareOffsetPrimeSupport n (primeWorldModulus S + r))

/-- This counts incidences, which may exceed the number of packets. -/
noncomputable def coarseCrossCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ pq ∈ coarseOutsideOrderedPairs S n, (coarseCrossOffsets S n pq.1 pq.2).card

/-- Exact transpose of actual supports, following the existing PacketCross pattern. -/
theorem coarseCrossCount_eq_support_products {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n : ℕ) :
    coarseCrossCount S n = ∑ r ∈ coarsePrimeWorldBase S n,
      (squareOffsetPrimeSupport n r).card *
        (squareOffsetPrimeSupport n (primeWorldModulus S + r)).card := by
  classical
  have hpairset (r : ℕ) (hr : r ∈ coarsePrimeWorldBase S n) :
      (coarseOutsideOrderedPairs S n).filter (fun pq =>
        pq.1 ∈ squareOffsetPrimeSupport n r ∧
        pq.2 ∈ squareOffsetPrimeSupport n (primeWorldModulus S + r)) =
      (squareOffsetPrimeSupport n r).product
        (squareOffsetPrimeSupport n (primeWorldModulus S + r)) := by
    ext pq
    rcases pq with ⟨p, q⟩
    simp only [coarseOutsideOrderedPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    have hd := ((mem_coarsePrimeWorldBase_iff_survivor hS).mp hr).2.2
    have hl := coarse_survivor_support_outside hd
    have hu := coarse_survivor_support_outside (coarsePrimeWorld_survivor_shift.mpr hd)
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨⟨⟨hl h.1, hu h.2⟩, ?_⟩, h⟩
      intro he
      subst q
      exact not_prime_dvd_both_coarsePoints hr (mem_squareOffsetPrimeSupport.mp h.1).1
        ⟨(mem_squareOffsetPrimeSupport.mp h.1).2.2, (mem_squareOffsetPrimeSupport.mp h.2).2.2⟩
  unfold coarseCrossCount
  simp only [coarseCrossOffsets, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_boole, hpairset r hr]
  simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_id]

/-- Full cover forces at least one actual ordered incidence per coarse packet. -/
theorem totient_le_coarseCrossCount_of_fullyCovered {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hfit : primeWorldModulus S ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    Nat.totient (primeWorldModulus S) ≤ coarseCrossCount S n := by
  rw [← card_coarsePrimeWorldBase S n, coarseCrossCount_eq_support_products hS n]
  calc
    (coarsePrimeWorldBase S n).card = ∑ r ∈ coarsePrimeWorldBase S n, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨p, q, _, _, _, hp, hq⟩ := exists_distinct_coarseOutside_cover_pair hS hfit hr hfull
      exact Nat.succ_le_of_lt (Nat.mul_pos (Finset.card_pos.mpr ⟨p, hp⟩) (Finset.card_pos.mpr ⟨q, hq⟩))

/-- Distinct prime directions impose a product period on collisions. -/
theorem coarseCrossOffsets_mul_dvd_diff {S : Finset ℕ} {n p q r s : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hr : r ∈ coarseCrossOffsets S n p q) (hs : s ∈ coarseCrossOffsets S n p q) :
    p * q ∣ s - r := by
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  exact crossPeriod_mul_dvd_diff ((Nat.coprime_primes hp hq).mpr hpq)
    (mem_squareOffsetPrimeSupport.mp hr'.1).2.2 (mem_squareOffsetPrimeSupport.mp hs'.1).2.2
    (mem_squareOffsetPrimeSupport.mp hr'.2).2.2 (mem_squareOffsetPrimeSupport.mp hs'.2).2.2

theorem card_coarseCrossOffsets_le_one {S : Finset ℕ} {n p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hfar : primeWorldModulus S < p * q) :
    (coarseCrossOffsets S n p q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hr' := mem_coarsePrimeWorldBase.mp (Finset.mem_filter.mp hr).1
  have hs' := mem_coarsePrimeWorldBase.mp (Finset.mem_filter.mp hs).1
  by_cases hrs : r ≤ s
  · have hd := coarseCrossOffsets_mul_dvd_diff hp hq hpq hr hs
    have hz := Nat.eq_zero_of_dvd_of_lt hd (show s - r < p * q by omega)
    omega
  · have hd := coarseCrossOffsets_mul_dvd_diff hp hq hpq hs hr
    have hz := Nat.eq_zero_of_dvd_of_lt hd (show r - s < p * q by omega)
    omega

/-- The near/far split uses period width M, rather than the original packet width n. -/
def coarseNearPairs (S : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (coarseOutsideOrderedPairs S n).filter (fun pq => pq.1 * pq.2 ≤ primeWorldModulus S)

def coarseFarPairs (S : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (coarseOutsideOrderedPairs S n).filter (fun pq => primeWorldModulus S < pq.1 * pq.2)

theorem coarseNear_union_far (S : Finset ℕ) (n : ℕ) :
    coarseNearPairs S n ∪ coarseFarPairs S n = coarseOutsideOrderedPairs S n := by
  ext pq
  by_cases h : pq.1 * pq.2 ≤ primeWorldModulus S
  · simp [coarseNearPairs, coarseFarPairs, h]
  · simp [coarseNearPairs, coarseFarPairs, h, lt_of_not_ge h]

theorem disjoint_coarseNear_far (S : Finset ℕ) (n : ℕ) :
    Disjoint (coarseNearPairs S n) (coarseFarPairs S n) := by
  apply Finset.disjoint_filter.mpr
  intro pq hpq hnear hfar
  omega

theorem coarseCrossCount_eq_near_add_far (S : Finset ℕ) (n : ℕ) :
    coarseCrossCount S n =
      (∑ pq ∈ coarseNearPairs S n, (coarseCrossOffsets S n pq.1 pq.2).card) +
      (∑ pq ∈ coarseFarPairs S n, (coarseCrossOffsets S n pq.1 pq.2).card) := by
  rw [← Finset.sum_union (disjoint_coarseNear_far S n), coarseNear_union_far]
  rfl

theorem coarseFar_sum_le_card (S : Finset ℕ) (n : ℕ) :
    (∑ pq ∈ coarseFarPairs S n, (coarseCrossOffsets S n pq.1 pq.2).card) ≤
      (coarseFarPairs S n).card := by
  classical
  calc
    _ ≤ ∑ pq ∈ coarseFarPairs S n, 1 := by
      apply Finset.sum_le_sum
      intro pq hpq
      have h := Finset.mem_filter.mp hpq
      have ho := Finset.mem_filter.mp h.1
      have ht := Finset.mem_product.mp ho.1
      have hp := (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp ht.1).1).1
      have hq := (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp ht.2).1).1
      exact card_coarseCrossOffsets_le_one hp hq ho.2 h.2
    _ = _ := by simp

/-- The exact necessary frontier retains near multiplicity and far direction capacity. -/
theorem coarseTown_assignment_frontier {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hfit : primeWorldModulus S ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    Nat.totient (primeWorldModulus S) ≤
      (∑ pq ∈ coarseNearPairs S n, (coarseCrossOffsets S n pq.1 pq.2).card) +
        (coarseFarPairs S n).card := by
  have hl := totient_le_coarseCrossCount_of_fullyCovered hS hfit hfull
  rw [coarseCrossCount_eq_near_add_far] at hl
  exact hl.trans (Nat.add_le_add_left (coarseFar_sum_le_card S n) _)

/-- The 018 world excludes every actual odd old-prime cover at a positive anchor. -/
theorem centeredOddGap_survivor_covered_only_two {n r p : ℕ} (hn : 0 < n)
    (hd : SupportDisjointFrom (centeredOddGapPrimeWorld n) (n ^ 2 + r))
    (hp : p ∈ squareOffsetPrimeSupport n r) : p = 2 := by
  have h := mem_squareOffsetPrimeSupport.mp hp
  by_contra hne
  apply hd h.1 h.2.2
  exact Finset.mem_erase.mpr ⟨hne, mem_primeScalesUpTo.mpr ⟨h.1, by omega⟩⟩

/-- Each individual packet already satisfies the existing family predicate. -/
theorem coarse_packet_oldSupport_family {S : Finset ℕ} {n r : ℕ}
    (hfit : primeWorldModulus S ≤ n) (hr : r ∈ coarsePrimeWorldBase S n) :
    PairwiseOldSupportDisjointSquareSeatFamily n {r, primeWorldModulus S + r} := by
  apply pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily
  have hseats := coarsePrimeWorldBase_squareOffsets hfit hr
  constructor
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hseats.1
    · exact hseats.2
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact coprime_coarsePrimeWorldPoints hr
    · exact (coprime_coarsePrimeWorldPoints hr).symm
    · exact False.elim (hab rfl)

/-- The odd-gap basis cannot cover an odd survivor through any old direction. -/
theorem centeredOddGap_odd_survivor_not_covered {n r : ℕ} (hn : 0 < n)
    (hd : SupportDisjointFrom (centeredOddGapPrimeWorld n) (n ^ 2 + r))
    (hodd : ¬ 2 ∣ n ^ 2 + r) : ¬ SquareOffsetCovered n r := by
  intro hc
  obtain ⟨p, hp⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp hc
  have he := centeredOddGap_survivor_covered_only_two hn hd hp
  exact hodd (he ▸ (mem_squareOffsetPrimeSupport.mp hp).2.2)

/-- A norm direction assigned in the coarse town retains the exact 018 order-four address. -/
theorem coarse_visibleNorm_direction {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n r p : ℕ} (hr : r ∈ coarsePrimeWorldBase S n)
    (hp : p ∈ squareOffsetPrimeSupport n r) (hN : p ∣ centeredFoldNorm n) :
    p ∉ S ∧ p % 4 = 1 ∧
      DkMath.NumberTheory.GapFocusing.primeOrder p n ((n + 1 : ℕ) : ℤ) = 4 := by
  have hp' := mem_squareOffsetPrimeSupport.mp hp
  exact ⟨((mem_coarsePrimeWorldBase_iff_survivor hS).mp hr).2.2 hp'.1 hp'.2.2,
    prime_dvd_centeredFoldNorm_mod_four hp'.1 hN,
    prime_dvd_centeredFoldNorm_order_four hp'.1 hN⟩

end DkMath.NumberTheory.Legendre
