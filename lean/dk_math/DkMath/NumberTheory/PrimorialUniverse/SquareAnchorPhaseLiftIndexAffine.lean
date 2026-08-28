/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndex
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexAffine"

/-!
# Fresh-prime lift-index affine geometry

The raw lift map is affine modulo a fresh prime.  The `+a`, `0`, and `-a`
indices from PUU-L022 therefore form a centrally symmetric triple on the
fresh-prime index circle.  This module remains finite provider-side
congruence geometry: it does not assert primality, escape, or a later
Legendre/analytic conclusion.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Affine residue map -/

/-- The raw lift has the affine residue formula modulo the fresh prime. -/
theorem primeBasisWheelLift_cast_freshPrime
    {S : Finset ℕ} {q b j : ℕ} :
    ((primeBasisWheelLift S b j : ℕ) : ZMod q) =
      (b : ZMod q) + (j : ZMod q) *
        (finitePrimeBasisProduct S : ZMod q) := by
  simp [primeBasisWheelLift, Nat.cast_add, Nat.cast_mul]

/-- The old period is nonzero modulo a fresh prime. -/
theorem finitePrimeBasisProduct_cast_ne_zero_of_freshPrime
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    (finitePrimeBasisProduct S : ZMod q) ≠ 0 := by
  intro hzero
  have hdiv : q ∣ finitePrimeBasisProduct S :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact ((Nat.Prime.coprime_iff_not_dvd hq).mp
    (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS)) hdiv

/-! ## Opposite offsets and midpoint -/

/-- The two phase offsets are opposite about the deleted index. -/
theorem freshPrime_phase_offsets_opposite
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (_hq2 : q ≠ 2)
    (_hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    ((jplus : ZMod q) - (jzero : ZMod q)) =
      -((jminus : ZMod q) - (jzero : ZMod q)) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hplus' := hplus.2
  have hminus' := hminus.2
  have hzero' : (primeBasisWheelLift S b jzero : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  rw [primeBasisWheelLift_cast_freshPrime] at hplus' hminus' hzero'
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hsum :
      (((jplus : ZMod q) - (jzero : ZMod q)) +
        ((jminus : ZMod q) - (jzero : ZMod q))) *
          (finitePrimeBasisProduct S : ZMod q) = 0 := by
    linear_combination hplus' + hminus' - 2 * hzero'
  have hsum' :
      ((jplus : ZMod q) - (jzero : ZMod q)) +
        ((jminus : ZMod q) - (jzero : ZMod q)) = 0 :=
    (mul_eq_zero.mp hsum).resolve_right hM
  exact eq_neg_of_add_eq_zero_left hsum'

/-- The deleted index is the affine midpoint of the two phase indices. -/
theorem freshPrime_deleted_index_is_phase_midpoint
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jplus : ZMod q) + (jminus : ZMod q) =
      2 * (jzero : ZMod q) := by
  have h := freshPrime_phase_offsets_opposite hS hq hqS hq2 hcop
    hplus hminus hzero
  linear_combination h

/-- A midpoint of the phase pair is unique modulo an odd fresh prime. -/
theorem freshPrime_phase_midpoint_unique
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero)
    {z : ZMod q}
    (hz : (jplus : ZMod q) + (jminus : ZMod q) = 2 * z) :
    z = (jzero : ZMod q) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h2zero
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h2zero
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hqge2 : 2 ≤ q := hq.two_le
    omega
  have hmid := freshPrime_deleted_index_is_phase_midpoint hS hq hqS hq2 hcop
    hplus hminus hzero
  apply mul_left_cancel₀ h2
  calc
    (2 : ZMod q) * z = (jplus : ZMod q) + (jminus : ZMod q) := hz.symm
    _ = 2 * (jzero : ZMod q) := hmid

/-- Reflection in the deleted index sends the plus phase index to the minus one. -/
theorem freshPrime_plus_reflects_to_minus_about_deleted
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    (jminus : ZMod q) =
      2 * (jzero : ZMod q) - (jplus : ZMod q) := by
  have hmid := freshPrime_deleted_index_is_phase_midpoint hS hq hqS hq2 hcop
    hplus hminus hzero
  linear_combination hmid

/-! ## Visible `6 -> 30` regression -/

/-- The indices `0, 4, 3` satisfy the affine identities modulo `5`. -/
theorem freshPrimeLiftIndexAffine_two_three_five_regression :
    ((0 : ZMod 5) - (4 : ZMod 5)) = -((3 : ZMod 5) - (4 : ZMod 5)) ∧
      (0 : ZMod 5) + (3 : ZMod 5) = 2 * (4 : ZMod 5) ∧
      (3 : ZMod 5) = 2 * (4 : ZMod 5) - (0 : ZMod 5) := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  rcases freshPrimeLiftIndex_two_three_five_regression with
    ⟨_, _, _, _, _, hplus, hminus, hzero, _, _, _⟩
  have hoff := freshPrime_phase_offsets_opposite hS
    (q := 5) (a := 1) (b := 1) (jplus := 0) (jminus := 3) (jzero := 4)
    (by norm_num) (by simp) (by norm_num) (by norm_num)
    hplus hminus hzero
  have hmid := freshPrime_deleted_index_is_phase_midpoint hS
    (q := 5) (a := 1) (b := 1) (jplus := 0) (jminus := 3) (jzero := 4)
    (by norm_num) (by simp) (by norm_num) (by norm_num)
    hplus hminus hzero
  have href := freshPrime_plus_reflects_to_minus_about_deleted hS
    (q := 5) (a := 1) (b := 1) (jplus := 0) (jminus := 3) (jzero := 4)
    (by norm_num) (by simp) (by norm_num) (by norm_num)
    hplus hminus hzero
  exact ⟨by simpa using hoff, by simpa using hmid, by simpa using href⟩

end DkMath.NumberTheory.PrimorialUniverse
