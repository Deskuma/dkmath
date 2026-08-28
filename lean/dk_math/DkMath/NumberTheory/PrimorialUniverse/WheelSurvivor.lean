/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor"

/-!
# Primorial wheel survivors and reflection

This module cuts one open interval of the finite reservation sheet from
PUU-L005.  A wheel survivor is a positive natural seat strictly below the
finite prime-basis product and reserved by none of the basis primes.  The
reflection `r ↦ M - r` preserves this predicate and is an involution on the
closed interval `r ≤ M`.

The survivor predicate is not a primality predicate: a composite natural can
survive the finite basis.  The module also records the optional reduced-residue
bridge, but does not count survivors with Euler's totient.  It makes no claim
about next-prime lifts, wheel gaps, Legendre, or analytic sieve statements.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open scoped BigOperators

/-! ## One-period survivor seats -/

/-- A positive seat strictly inside one finite prime-basis period. -/
def IsPrimeBasisWheelSurvivor (S : Finset ℕ) (r : ℕ) : Prop :=
  0 < r ∧
    r < finitePrimeBasisProduct S ∧
      ¬ ReservedByPrimeBasis S r

/-- The finite set of one-period seats that survive every basis prime. -/
noncomputable def primeBasisWheelSurvivors (S : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (finitePrimeBasisProduct S - 1)).filter
    (fun r => ¬ ReservedByPrimeBasis S r)

@[simp] theorem mem_primeBasisWheelSurvivors_iff
    {S : Finset ℕ} {r : ℕ} :
    r ∈ primeBasisWheelSurvivors S ↔
      IsPrimeBasisWheelSurvivor S r := by
  simp only [primeBasisWheelSurvivors, Finset.mem_filter, Finset.mem_Icc]
  unfold IsPrimeBasisWheelSurvivor
  constructor
  · rintro ⟨⟨hr1, hrM⟩, hNot⟩
    exact ⟨by omega, by omega, hNot⟩
  · rintro ⟨hr0, hrM, hNot⟩
    exact ⟨⟨by omega, by omega⟩, hNot⟩

/-! ## Reduced-residue bridge -/

/-- Avoiding all basis primes is equivalent to coprimality with their product. -/
theorem not_reserved_iff_coprime_finitePrimeBasisProduct
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (r : ℕ) :
    ¬ ReservedByPrimeBasis S r ↔
      Nat.Coprime r (finitePrimeBasisProduct S) := by
  constructor
  · intro hNot
    unfold finitePrimeBasisProduct
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    rw [Nat.coprime_comm, (hS p hp).coprime_iff_not_dvd]
    intro hpR
    exact hNot ⟨p, hp, hpR⟩
  · intro hC hReserved
    unfold finitePrimeBasisProduct at hC
    rw [Nat.coprime_prod_right_iff] at hC
    obtain ⟨p, hp, hpR⟩ := hReserved
    have hpC : Nat.Coprime r p := hC p hp
    rw [Nat.coprime_comm, (hS p hp).coprime_iff_not_dvd] at hpC
    exact hpC hpR

/-! ## Exact reflection symmetry -/

/-- Reservation at `r` and at its interior reflection `M - r` agree. -/
theorem reserved_reflect_iff
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    {r : ℕ} (_hr0 : 0 < r)
    (hrM : r < finitePrimeBasisProduct S) :
    ReservedByPrimeBasis S
        (finitePrimeBasisProduct S - r) ↔
      ReservedByPrimeBasis S r := by
  have hrle : r ≤ finitePrimeBasisProduct S := Nat.le_of_lt hrM
  have hSplit : finitePrimeBasisProduct S - r + r =
      finitePrimeBasisProduct S := Nat.sub_add_cancel hrle
  have hDiv : ∀ p ∈ S,
      p ∣ finitePrimeBasisProduct S - r ↔ p ∣ r := by
    intro p hp
    have hpM : p ∣ finitePrimeBasisProduct S :=
      mem_dvd_finitePrimeBasisProduct hp
    constructor
    · intro hpSub
      have hpSplit : p ∣ finitePrimeBasisProduct S - r + r := by
        rw [hSplit]
        exact hpM
      have hpSplit' : p ∣ r + (finitePrimeBasisProduct S - r) := by
        simpa [Nat.add_comm] using hpSplit
      exact (Nat.dvd_add_left hpSub).mp hpSplit'
    · intro hpR
      have hpSplit : p ∣ r + (finitePrimeBasisProduct S - r) := by
        rw [Nat.add_comm, hSplit]
        exact hpM
      exact (Nat.dvd_add_right hpR).mp hpSplit
  constructor
  · rintro ⟨p, hp, hpReflected⟩
    exact ⟨p, hp, (hDiv p hp).mp hpReflected⟩
  · rintro ⟨p, hp, hpR⟩
    exact ⟨p, hp, (hDiv p hp).mpr hpR⟩

/-- Reflection preserves one-period wheel survivors. -/
theorem wheelSurvivor_reflect
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {r : ℕ} (hr : IsPrimeBasisWheelSurvivor S r) :
    IsPrimeBasisWheelSurvivor S
      (finitePrimeBasisProduct S - r) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.sub_pos_of_lt hr.2.1
  · exact Nat.sub_lt_of_pos_le hr.1 (Nat.le_of_lt hr.2.1)
  · intro hReserved
    exact hr.2.2 ((reserved_reflect_iff hS hr.1 hr.2.1).mp hReserved)

/-- Subtracting twice from a period returns the original seat. -/
theorem wheelReflection_involutive
    {S : Finset ℕ} {r : ℕ}
    (hr : r ≤ finitePrimeBasisProduct S) :
    finitePrimeBasisProduct S -
        (finitePrimeBasisProduct S - r) = r := by
  exact Nat.sub_sub_self hr

/-! ## Small wheel regression -/

theorem primeBasisWheelSurvivors_two_three :
    primeBasisWheelSurvivors ({2, 3} : Finset ℕ) = {1, 5} := by
  ext r
  rw [mem_primeBasisWheelSurvivors_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hr
    have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by
      decide
    unfold IsPrimeBasisWheelSurvivor at hr
    rw [hM] at hr
    have hrne2 : r ≠ 2 := by
      intro hr2
      subst r
      exact hr.2.2 (by norm_num [ReservedByPrimeBasis])
    have hrne3 : r ≠ 3 := by
      intro hr3
      subst r
      exact hr.2.2 (by norm_num [ReservedByPrimeBasis])
    have hrne4 : r ≠ 4 := by
      intro hr4
      subst r
      exact hr.2.2 (by norm_num [ReservedByPrimeBasis])
    omega
  · intro hr
    rcases hr with rfl | rfl <;>
      norm_num [IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis,
        finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
