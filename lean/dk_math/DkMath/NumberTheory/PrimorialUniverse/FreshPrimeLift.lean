/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift"

/-!
# Fresh-prime lifts

Let `M = finitePrimeBasisProduct S` and let `q` be a fresh ordinary prime.
Each old one-period survivor `r` gives the `q` lifts `r + j * M` for
`j < q`.  The old reservation status is constant on this fiber, while the
new prime `q` divides exactly one lift.  Thus the local fiber has `q - 1`
survivors after adjoining `q`.

The fresh prime is only required to be outside `S`; it is not assumed to be
the numerically next prime.  This module proves the per-old-survivor local
deletion theorem, not the global next-wheel decomposition or cardinality
recurrence.  Survivors remain finite-basis survivors rather than primality
witnesses, and no Legendre or prime-density statement is made.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open scoped BigOperators

/-! ## Lift vocabulary and period arithmetic -/

/-- The `j`-th lift of an old seat across the old product period. -/
def primeBasisWheelLift (S : Finset ℕ) (r j : ℕ) : ℕ :=
  r + j * finitePrimeBasisProduct S

/-- Adjoining a fresh prime multiplies the old product period by that prime. -/
theorem finitePrimeBasisProduct_insert
    {S : Finset ℕ} {q : ℕ} (hqS : q ∉ S) :
    finitePrimeBasisProduct (insert q S) =
      q * finitePrimeBasisProduct S := by
  simp [finitePrimeBasisProduct, hqS]

/-- A fresh prime is coprime to the product of the old prime basis. -/
theorem freshPrime_coprime_finitePrimeBasisProduct
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    Nat.Coprime q (finitePrimeBasisProduct S) := by
  unfold finitePrimeBasisProduct
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  apply (Nat.coprime_primes hq (hS p hp)).mpr
  intro hqp
  apply hqS
  simpa [hqp] using hp

/-- Old-prime reservation is unchanged along every lift fiber. -/
theorem reservedByPrimeBasis_lift_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (r j : ℕ) :
    ReservedByPrimeBasis S (primeBasisWheelLift S r j) ↔
      ReservedByPrimeBasis S r := by
  simpa [primeBasisWheelLift] using
    (reservedByPrimeBasis_add_mul_period_iff hS r j)

theorem not_reservedByPrimeBasis_lift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {r j : ℕ} (hr : IsPrimeBasisWheelSurvivor S r) :
    ¬ ReservedByPrimeBasis S (primeBasisWheelLift S r j) := by
  intro hLift
  exact hr.2.2 ((reservedByPrimeBasis_lift_iff hS r j).mp hLift)

/-- Every old survivor lift lies strictly inside the enlarged period. -/
theorem primeBasisWheelLift_mem_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (hqS : q ∉ S)
    {r j : ℕ} (hr : IsPrimeBasisWheelSurvivor S r)
    (hj : j < q) :
    0 < primeBasisWheelLift S r j ∧
      primeBasisWheelLift S r j <
        finitePrimeBasisProduct (insert q S) := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  constructor
  · unfold primeBasisWheelLift
    exact Nat.lt_of_lt_of_le hr.1 (Nat.le_add_right _ _)
  · unfold primeBasisWheelLift
    rw [finitePrimeBasisProduct_insert hqS]
    calc
      r + j * finitePrimeBasisProduct S <
          finitePrimeBasisProduct S + j * finitePrimeBasisProduct S :=
        Nat.add_lt_add_right hr.2.1 _
      _ = (j + 1) * finitePrimeBasisProduct S := by
        simp [Nat.succ_mul, Nat.add_comm]
      _ ≤ q * finitePrimeBasisProduct S := by
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)

/-! ## The unique fresh-prime deletion -/

/-- Among the first `q` lifts, exactly one is divisible by the fresh prime. -/
theorem existsUnique_freshPrime_dvd_lift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {r : ℕ} (_hr : IsPrimeBasisWheelSurvivor S r) :
    ∃! j : ℕ,
      j < q ∧ q ∣ primeBasisWheelLift S r j := by
  have hcop : Nat.Coprime (finitePrimeBasisProduct S) q :=
    (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS).symm
  have hq0 : q ≠ 0 := hq.ne_zero
  obtain ⟨j, hj, hjMod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime
      (q - r % q) hcop hq0
  have hrMod : r % q < q := Nat.mod_lt _ hq.pos
  have hSumMod : (r % q + (q - r % q) % q) % q = 0 := by
    by_cases hrZero : r % q = 0
    · simp [hrZero]
    · have hSubLt : q - r % q < q :=
        Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero hrZero) hrMod.le
      rw [Nat.mod_eq_of_lt hSubLt]
      have hSum : r % q + (q - r % q) = q := by omega
      rw [hSum, Nat.mod_self]
  have hDiv : q ∣ primeBasisWheelLift S r j := by
    rw [Nat.dvd_iff_mod_eq_zero]
    unfold primeBasisWheelLift
    rw [Nat.add_mod, Nat.mul_comm j, hjMod]
    exact hSumMod
  refine ⟨j, ⟨hj, hDiv⟩, ?_⟩
  intro j' hj'
  rcases Nat.le_total j j' with hjle | hj'le
  · have hDiffLift : q ∣
        primeBasisWheelLift S r j' - primeBasisWheelLift S r j :=
      Nat.dvd_sub hj'.2 hDiv
    have hDiff : q ∣ (j' - j) * finitePrimeBasisProduct S := by
      simpa [primeBasisWheelLift, Nat.add_sub_add_left, Nat.sub_mul] using hDiffLift
    have hDiffDvd : q ∣ j' - j := hcop.symm.dvd_of_dvd_mul_right hDiff
    have hDiffLt : j' - j < q :=
      lt_of_le_of_lt (Nat.sub_le _ _) hj'.1
    have hDiffZero := Nat.eq_zero_of_dvd_of_lt hDiffDvd hDiffLt
    omega
  · have hDiffLift : q ∣
        primeBasisWheelLift S r j - primeBasisWheelLift S r j' :=
      Nat.dvd_sub hDiv hj'.2
    have hDiff : q ∣ (j - j') * finitePrimeBasisProduct S := by
      simpa [primeBasisWheelLift, Nat.add_sub_add_left, Nat.sub_mul] using hDiffLift
    have hDiffDvd : q ∣ j - j' := hcop.symm.dvd_of_dvd_mul_right hDiff
    have hDiffLt : j - j' < q :=
      lt_of_le_of_lt (Nat.sub_le _ _) hj
    have hDiffZero := Nat.eq_zero_of_dvd_of_lt hDiffDvd hDiffLt
    omega

/-! ## The enlarged reservation sheet -/

/-- On an old-survivor fiber, `q` is the only new reservation channel. -/
theorem reservedByPrimeBasis_insert_fresh_lift_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {r j : ℕ} (hr : IsPrimeBasisWheelSurvivor S r) :
    ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r j) ↔
      q ∣ primeBasisWheelLift S r j := by
  have hOld : ¬ ReservedByPrimeBasis S (primeBasisWheelLift S r j) :=
    not_reservedByPrimeBasis_lift (j := j) hS hr
  constructor
  · rintro ⟨p, hp, hpDiv⟩
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hpDiv
    · exact (hOld ⟨p, hpS, hpDiv⟩).elim
  · intro hqDiv
    exact ⟨q, Finset.mem_insert_self q S, hqDiv⟩

/-- Exactly one lift is reserved after adjoining the fresh prime. -/
theorem existsUnique_reservedByPrimeBasis_insert_fresh_lift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {r : ℕ} (hr : IsPrimeBasisWheelSurvivor S r) :
    ∃! j : ℕ,
      j < q ∧
        ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r j) := by
  obtain ⟨j, hj, hUnique⟩ :=
    existsUnique_freshPrime_dvd_lift hS hq hqS hr
  refine ⟨j, ⟨hj.1, (reservedByPrimeBasis_insert_fresh_lift_iff
    hS hq hqS hr).mpr hj.2⟩, ?_⟩
  intro j' hj'
  apply hUnique j'
  exact ⟨hj'.1, (reservedByPrimeBasis_insert_fresh_lift_iff
    hS hq hqS hr).mp hj'.2⟩

/-! ## The `6 → 30` local regression -/

theorem primeBasisWheelLift_two_three_one_deleted :
    primeBasisWheelLift ({2, 3} : Finset ℕ) 1 4 = 25 ∧
      4 < 5 ∧ 5 ∣ primeBasisWheelLift ({2, 3} : Finset ℕ) 1 4 := by
  norm_num [primeBasisWheelLift, finitePrimeBasisProduct]

theorem primeBasisWheelLift_two_three_five_deleted :
    primeBasisWheelLift ({2, 3} : Finset ℕ) 5 0 = 5 ∧
      0 < 5 ∧ 5 ∣ primeBasisWheelLift ({2, 3} : Finset ℕ) 5 0 := by
  norm_num [primeBasisWheelLift, finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
