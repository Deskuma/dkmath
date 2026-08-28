/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.WheelReplication"

/-!
# Global finite-wheel replication

For a nonempty finite prime basis `S`, a fresh prime `q` replicates each old
survivor into `q` lift positions and deletes exactly one position in that
fiber.  This module proves the resulting global decomposition and cardinality
recurrence.  The empty basis is deliberately excluded from the recurrence:
its period is `1`, so it has no old survivor while the one-prime wheel is
nonempty.

The proof uses quotient/remainder decomposition by the old period, local
unique deletion from PUU-L007, and injectivity of the lift representation.
It does not identify the cardinality with Euler's totient and does not assert
that a survivor is prime.  Global wheel-gap, analytic, Legendre, PowerSwap,
and GN/CosmicFormula statements are outside this checkpoint.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open scoped BigOperators

/-! ## The old period and canonical decomposition -/

/-- A nonempty finite prime basis has a product period strictly larger than one. -/
theorem one_lt_finitePrimeBasisProduct_of_nonempty
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty) :
    1 < finitePrimeBasisProduct S := by
  obtain ⟨p, hp⟩ := hSne
  have hpM : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hp
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  exact lt_of_lt_of_le (hS p hp).one_lt (Nat.le_of_dvd hMpos hpM)

/-- Every enlarged survivor has a unique old-survivor lift representation. -/
theorem enlargedWheelSurvivor_iff_exists_oldSurvivorLift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {x : ℕ} :
    IsPrimeBasisWheelSurvivor (insert q S) x ↔
      ∃ r j : ℕ,
        IsPrimeBasisWheelSurvivor S r ∧
        j < q ∧
        x = primeBasisWheelLift S r j ∧
        ¬ q ∣ x := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hMgt : 1 < finitePrimeBasisProduct S :=
    one_lt_finitePrimeBasisProduct_of_nonempty hS hSne
  constructor
  · intro hx
    let r := x % finitePrimeBasisProduct S
    let j := x / finitePrimeBasisProduct S
    have hDecomp : x = r + j * finitePrimeBasisProduct S := by
      dsimp [r, j]
      rw [Nat.mod_add_div' x (finitePrimeBasisProduct S)]
    have hrM : r < finitePrimeBasisProduct S :=
      Nat.mod_lt _ hMpos
    have hjq : j < q := by
      have hMj : finitePrimeBasisProduct S * j ≤ x := by
        rw [hDecomp]
        rw [Nat.mul_comm j]
        exact Nat.le_add_left _ _
      have hMq : finitePrimeBasisProduct S * j <
          finitePrimeBasisProduct S * q := by
        apply lt_of_le_of_lt hMj
        have hxBound : x < finitePrimeBasisProduct (insert q S) := hx.2.1
        rw [finitePrimeBasisProduct_insert hqS] at hxBound
        simpa [Nat.mul_comm] using hxBound
      exact (Nat.mul_lt_mul_left hMpos).mp hMq
    have hOldNot : ¬ ReservedByPrimeBasis S r := by
      intro hrRes
      have hxOld : ReservedByPrimeBasis S x := by
        rw [hDecomp]
        exact (reservedByPrimeBasis_lift_iff hS r j).mpr hrRes
      obtain ⟨p, hp, hpX⟩ := hxOld
      exact hx.2.2 ⟨p, Finset.mem_insert_of_mem hp, hpX⟩
    have hrPos : 0 < r := by
      by_contra hrZero
      have hrEq : r = 0 := Nat.eq_zero_of_not_pos hrZero
      obtain ⟨p, hp⟩ := hSne
      exact hOldNot ⟨p, hp, by simp [hrEq]⟩
    have hr : IsPrimeBasisWheelSurvivor S r := ⟨hrPos, hrM, hOldNot⟩
    have hqNot : ¬ q ∣ x := by
      intro hqX
      exact hx.2.2 ⟨q, Finset.mem_insert_self q S, hqX⟩
    exact ⟨r, j, hr, hjq, hDecomp, hqNot⟩
  · rintro ⟨r, j, hr, hj, rfl, hqNot⟩
    have hRange := primeBasisWheelLift_mem_enlarged_period hS hq hqS hr hj
    refine ⟨hRange.1, hRange.2, ?_⟩
    intro hReserved
    exact hqNot ((reservedByPrimeBasis_insert_fresh_lift_iff
      hS hq hqS hr).mp hReserved)

/-- Lift coordinates are injective when both remainders lie below the old period. -/
theorem primeBasisWheelLift_injective_on_period
    {S : Finset ℕ} {r r' j j' : ℕ}
    (hrM : r < finitePrimeBasisProduct S)
    (hr'M : r' < finitePrimeBasisProduct S)
    (hEq : primeBasisWheelLift S r j = primeBasisWheelLift S r' j') :
    r = r' ∧ j = j' := by
  have hRem : r = r' := by
    have hMod := congrArg (fun x => x % finitePrimeBasisProduct S) hEq
    simpa [primeBasisWheelLift, Nat.add_mod, Nat.mul_mod_left,
      Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt hr'M] using hMod
  have hEq' : r + j * finitePrimeBasisProduct S =
      r + j' * finitePrimeBasisProduct S := by
    simpa [primeBasisWheelLift, hRem] using hEq
  have hMpos : 0 < finitePrimeBasisProduct S := by
    exact lt_of_le_of_lt (Nat.zero_le _) hrM
  exact ⟨hRem, Nat.mul_right_cancel hMpos (Nat.add_left_cancel hEq')⟩

/-! ## Local surviving index sets -/

/-- The indices below `q` whose lifts are not deleted by the fresh prime. -/
noncomputable def freshPrimeSurvivingLiftIndices
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter
    (fun j => ¬ q ∣ primeBasisWheelLift S r j)

@[simp] theorem mem_freshPrimeSurvivingLiftIndices_iff
    {S : Finset ℕ} {q r j : ℕ} :
    j ∈ freshPrimeSurvivingLiftIndices S q r ↔
      j < q ∧ ¬ q ∣ primeBasisWheelLift S r j := by
  classical
  simp [freshPrimeSurvivingLiftIndices]

/-- One old-survivor fiber has exactly `q - 1` surviving lift indices. -/
theorem card_freshPrimeSurvivingLiftIndices
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {r : ℕ} (hr : IsPrimeBasisWheelSurvivor S r) :
    (freshPrimeSurvivingLiftIndices S q r).card = q - 1 := by
  classical
  obtain ⟨j₀, hj₀, hUnique⟩ :=
    existsUnique_freshPrime_dvd_lift hS hq hqS hr
  have hSet : freshPrimeSurvivingLiftIndices S q r =
      (Finset.range q).erase j₀ := by
    ext j
    rw [mem_freshPrimeSurvivingLiftIndices_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hj, hNot⟩
      refine ⟨?_, Finset.mem_range.mpr hj⟩
      intro hEq
      apply hNot
      rw [hEq]
      exact hj₀.2
    · rintro ⟨hjne, hj⟩
      refine ⟨Finset.mem_range.mp hj, ?_⟩
      intro hDiv
      exact hjne (hUnique j ⟨Finset.mem_range.mp hj, hDiv⟩)
  rw [hSet, Finset.card_erase_of_mem (Finset.mem_range.mpr hj₀.1),
    Finset.card_range]

/-! ## Global lift image and cardinality -/

/-- The finite set of seats obtained from all old surviving lift fibers. -/
noncomputable def primeBasisWheelSurvivorLiftSeats
    (S : Finset ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact ((primeBasisWheelSurvivors S).sigma
    (fun r => freshPrimeSurvivingLiftIndices S q r)).image
      (fun x => primeBasisWheelLift S x.1 x.2)

/-- The enlarged wheel is exactly the image of its surviving old lift fibers. -/
theorem primeBasisWheelSurvivor_insert_fresh_eq_liftSeats
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    primeBasisWheelSurvivors (insert q S) =
      primeBasisWheelSurvivorLiftSeats S q := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r, j, hr, hj, hxLift, hqNot⟩ :=
      (enlargedWheelSurvivor_iff_exists_oldSurvivorLift hS hSne hq hqS).mp
        (mem_primeBasisWheelSurvivors_iff.mp hx)
    apply Finset.mem_image.mpr
    refine ⟨⟨r, j⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨mem_primeBasisWheelSurvivors_iff.mpr hr, ?_⟩
      exact mem_freshPrimeSurvivingLiftIndices_iff.mpr ⟨hj, by
        simpa [hxLift] using hqNot⟩
    · exact hxLift.symm
  · intro hx
    obtain ⟨⟨r, j⟩, hSigma, rfl⟩ := Finset.mem_image.mp hx
    have hSigma' := Finset.mem_sigma.mp hSigma
    have hr := mem_primeBasisWheelSurvivors_iff.mp hSigma'.1
    have hj := mem_freshPrimeSurvivingLiftIndices_iff.mp hSigma'.2
    apply mem_primeBasisWheelSurvivors_iff.mpr
    exact (enlargedWheelSurvivor_iff_exists_oldSurvivorLift hS hSne hq hqS).mpr
      ⟨r, j, hr, hj.1, rfl, hj.2⟩

/-- The lift image has no collisions between distinct old survivor fibers. -/
theorem primeBasisWheelSurvivorLiftSeats_card
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (_hqS : q ∉ S) :
    (primeBasisWheelSurvivorLiftSeats S q).card =
      ((primeBasisWheelSurvivors S).sigma
        (fun r => freshPrimeSurvivingLiftIndices S q r)).card := by
  classical
  unfold primeBasisWheelSurvivorLiftSeats
  apply Finset.card_image_iff.mpr
  intro a ha b hb hEq
  have ha' := Finset.mem_sigma.mp ha
  have hb' := Finset.mem_sigma.mp hb
  have hRep := primeBasisWheelLift_injective_on_period
    (mem_primeBasisWheelSurvivors_iff.mp ha'.1).2.1
    (mem_primeBasisWheelSurvivors_iff.mp hb'.1).2.1 hEq
  rcases hRep with ⟨hr, hj⟩
  exact Sigma.ext hr (heq_of_eq hj)

/-- Global wheel replication: adjoining a fresh prime multiplies survivors by `q - 1`. -/
theorem card_primeBasisWheelSurvivors_insert_fresh
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    (primeBasisWheelSurvivors (insert q S)).card =
      (q - 1) * (primeBasisWheelSurvivors S).card := by
  classical
  rw [primeBasisWheelSurvivor_insert_fresh_eq_liftSeats hS hSne hq hqS,
    primeBasisWheelSurvivorLiftSeats_card hS hq hqS,
    Finset.card_sigma]
  have hLocal : ∀ r ∈ primeBasisWheelSurvivors S,
      (freshPrimeSurvivingLiftIndices S q r).card = q - 1 := by
    intro r hr
    exact card_freshPrimeSurvivingLiftIndices hS hq hqS
      (mem_primeBasisWheelSurvivors_iff.mp hr)
  calc
    (∑ r ∈ primeBasisWheelSurvivors S,
        (freshPrimeSurvivingLiftIndices S q r).card) =
        ∑ r ∈ primeBasisWheelSurvivors S, (q - 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hLocal r hr
    _ = (q - 1) * (primeBasisWheelSurvivors S).card := by
      simp [Nat.mul_comm]

/-! ## Visible wheel-growth regression -/

theorem card_primeBasisWheelSurvivors_two_three :
    (primeBasisWheelSurvivors ({2, 3} : Finset ℕ)).card = 2 := by
  rw [show primeBasisWheelSurvivors ({2, 3} : Finset ℕ) = {1, 5} by
    exact primeBasisWheelSurvivors_two_three]
  decide

theorem card_primeBasisWheelSurvivors_insert_five :
    (primeBasisWheelSurvivors ({2, 3, 5} : Finset ℕ)).card =
      (5 - 1) * (primeBasisWheelSurvivors ({2, 3} : Finset ℕ)).card := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by norm_num
  have hSet : insert 5 ({2, 3} : Finset ℕ) =
      ({2, 3, 5} : Finset ℕ) := by
    decide
  simpa only [hSet] using
    card_primeBasisWheelSurvivors_insert_fresh hS hSne hq hqS

end DkMath.NumberTheory.PrimorialUniverse
