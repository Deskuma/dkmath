/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiberProjection
import DkMath.NumberTheory.PrimorialUniverse.WheelProjection
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSurvivorSubcover"

/-!
# Square-phase survivor subcovers

For a nonempty finite prime basis, the phase fiber of a coprime anchor is a
subfamily of the one-period wheel survivors.  After adjoining a fresh odd
prime, the two-sheet phase projection fiber is consequently a subcover of the
`q - 1`-seat wheel-survivor projection fiber.

This module records only finite congruence geometry.  In particular, a
survivor seat is not a prime-existence witness, and no escape, Legendre,
PowerSwap, GN/CosmicFormula, PNT, or RH statement is introduced.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Phase fibers are survivor seats -/

/-! A coprime-anchor phase-fiber element avoids every prime in the basis. -/
theorem squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a b : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    IsPrimeBasisWheelSurvivor S b := by
  have hb' := mem_squareAnchorPhaseFiber.mp hb
  have hprofile : SameSquarePrimeSignProfile S a b :=
    (sameSquareAnchorPhase_iff_primeSignProfile hS).mp hb'.2
  have hnot : ¬ ReservedByPrimeBasis S b := by
    rintro ⟨p, hpS, hpb⟩
    have hzero : (b : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff b p).mpr hpb
    rcases hprofile p hpS with h | h
    · exact prime_anchor_cast_ne_zero hS hcop hpS (h.trans hzero)
    · apply prime_anchor_cast_ne_zero hS hcop hpS
      calc
        (a : ZMod p) = -(b : ZMod p) := h
        _ = 0 := by rw [hzero]; simp
  have hbpos : 0 < b := by
    by_contra hbnot
    have hbzero : b = 0 := Nat.eq_zero_of_not_pos hbnot
    obtain ⟨p, hpS⟩ := hSne
    apply hnot
    exact ⟨p, hpS, by simp [hbzero]⟩
  exact ⟨hbpos, hb'.1, hnot⟩

/-! The whole coprime phase fiber is contained in the wheel survivor set. -/
theorem squareAnchorPhaseFiber_subset_primeBasisWheelSurvivors
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S)) :
    squareAnchorPhaseFiber S a ⊆ primeBasisWheelSurvivors S := by
  intro b hb
  exact mem_primeBasisWheelSurvivors_iff.mpr
    (squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
      hS hSne hcop hb)

/-! The phase-fiber cardinality is bounded by the survivor cardinality. -/
theorem squareAnchorPhaseFiber_card_le_primeBasisWheelSurvivors
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S)) :
    (squareAnchorPhaseFiber S a).card ≤ (primeBasisWheelSurvivors S).card :=
  Finset.card_le_card (squareAnchorPhaseFiber_subset_primeBasisWheelSurvivors
    hS hSne hcop)

/-! ## The fresh-prime projection is a subcover -/

/-! The phase projection fiber sits inside the corresponding wheel fiber. -/
theorem squareAnchorPhaseProjectionFiber_subset_wheelProjectionFiber
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (_hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (_hb : b ∈ squareAnchorPhaseFiber S a) :
    squareAnchorPhaseProjectionFiber S q a b ⊆
      primeBasisWheelProjectionFiber S q b := by
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  have hSne' : (insert q S : Finset ℕ).Nonempty := by simp
  have hsub := squareAnchorPhaseFiber_subset_primeBasisWheelSurvivors
    (S := insert q S) hS' hSne' hcop
  intro x hx
  have hx' := mem_squareAnchorPhaseProjectionFiber.mp hx
  apply Finset.mem_filter.mpr
  exact ⟨hsub hx'.1, hx'.2⟩

/-! The two local cardinalities can be read together. -/
theorem squareAnchorPhaseProjectionFiber_card_two_and_wheel_card
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (squareAnchorPhaseProjectionFiber S q a b).card = 2 ∧
      (primeBasisWheelProjectionFiber S q b).card = q - 1 := by
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact dvd_mul_left _ _)) hb
  exact ⟨card_squareAnchorPhaseProjectionFiber_fresh_odd
      hS hq hqS hq2 hcop hb,
    card_primeBasisWheelProjectionFiber hS hSne hq hqS hsurv⟩

/-! For an odd fresh prime, the wheel fiber has at least the two phase seats. -/
theorem two_le_fresh_wheel_projection_fiber_card
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    2 ≤ (primeBasisWheelProjectionFiber S q b).card := by
  rw [card_primeBasisWheelProjectionFiber hS hSne hq hqS
    (squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor hS hSne
      (hcop.of_dvd_right (by
        rw [finitePrimeBasisProduct_insert hqS]
        exact dvd_mul_left _ _)) hb)]
  have hqge3 : 3 ≤ q := by
    have hqge2 := hq.two_le
    omega
  omega

/-! ## The special fresh prime `3` -/

/-! For fresh `3`, the two-sheet phase fiber equals the wheel fiber. -/
theorem squareAnchorPhaseProjectionFiber_eq_wheelProjectionFiber_of_q_eq_three
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a b : ℕ}
    (h3S : 3 ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert 3 S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    squareAnchorPhaseProjectionFiber S 3 a b =
      primeBasisWheelProjectionFiber S 3 b := by
  have hsub := squareAnchorPhaseProjectionFiber_subset_wheelProjectionFiber
    hS hSne Nat.prime_three h3S (by norm_num) hcop hb
  apply Finset.eq_of_subset_of_card_le hsub
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert h3S]
      exact dvd_mul_left _ _)) hb
  rw [card_primeBasisWheelProjectionFiber hS hSne Nat.prime_three h3S hsurv]
  rw [card_squareAnchorPhaseProjectionFiber_fresh_odd
    hS Nat.prime_three h3S (by norm_num) hcop hb]

/-! A fresh prime strictly above `3` gives a proper two-of-`q-1` subcover. -/
theorem squareAnchorPhaseProjectionFiber_card_lt_wheelProjectionFiber_card
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hq3 : 3 < q)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (squareAnchorPhaseProjectionFiber S q a b).card <
      (primeBasisWheelProjectionFiber S q b).card := by
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact dvd_mul_left _ _)) hb
  rw [card_squareAnchorPhaseProjectionFiber_fresh_odd
      hS hq hqS hq2 hcop hb,
    card_primeBasisWheelProjectionFiber hS hSne hq hqS hsurv]
  omega

/-! ## Visible `6 -> 30` regression -/

/-! The phase fibers are the two-of-four subcovers in the `6 -> 30` tower. -/
theorem squareAnchorPhaseSurvivorSubcover_two_three_five_regression :
    squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 1 =
        ({1, 19} : Finset ℕ) ∧
      squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 5 =
        ({11, 29} : Finset ℕ) ∧
      primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 1 =
        ({1, 7, 13, 19} : Finset ℕ) ∧
      primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 5 =
        ({11, 17, 23, 29} : Finset ℕ) := by
  have hwheel1 := primeBasisWheelProjectionFiber_two_three_five_one
  have hwheel5 := primeBasisWheelProjectionFiber_two_three_five_five
  refine ⟨?_, ?_, hwheel1, hwheel5⟩
  · ext x
    constructor
    · intro hx
      have hx' := mem_squareAnchorPhaseProjectionFiber.mp hx
      have hxbound := (mem_squareAnchorPhaseFiber.mp hx'.1).1
      have hxbound' : x < 30 := by
        simpa [finitePrimeBasisProduct] using hxbound
      interval_cases x <;>
        norm_num [squareAnchorPhaseProjectionFiber, squareAnchorPhaseFiber,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          SameSquareAnchorPhase, finitePrimeBasisProduct] at hx
      all_goals simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;>
        norm_num [squareAnchorPhaseProjectionFiber, squareAnchorPhaseFiber,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          SameSquareAnchorPhase, finitePrimeBasisProduct]
  · ext x
    constructor
    · intro hx
      have hx' := mem_squareAnchorPhaseProjectionFiber.mp hx
      have hxbound := (mem_squareAnchorPhaseFiber.mp hx'.1).1
      have hxbound' : x < 30 := by
        simpa [finitePrimeBasisProduct] using hxbound
      interval_cases x <;>
        norm_num [squareAnchorPhaseProjectionFiber, squareAnchorPhaseFiber,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          SameSquareAnchorPhase, finitePrimeBasisProduct] at hx
      all_goals simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;>
        norm_num [squareAnchorPhaseProjectionFiber, squareAnchorPhaseFiber,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          SameSquareAnchorPhase, finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
