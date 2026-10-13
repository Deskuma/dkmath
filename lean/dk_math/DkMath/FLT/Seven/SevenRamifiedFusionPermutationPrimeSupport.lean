/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport"

namespace DkMath.FLT.Seven

/-- The seventh-power map is injective on the entire prime field, including zero. -/
theorem zmod_seventh_power_injective {ℓ : ℕ} (hp : Nat.Prime ℓ)
    (hcop : Nat.Coprime 7 (ℓ - 1)) :
    Function.Injective (fun x : ZMod ℓ => x ^ 7) := by
  have : Fact (Nat.Prime ℓ) := ⟨hp⟩
  have hc : Nat.Coprime (Nat.card ((ZMod ℓ)ˣ)) 7 := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hcop.symm
  have hi := hc.pow_left_bijective (G := (ZMod ℓ)ˣ) |>.injective
  intro x y h
  by_cases hx : x = 0
  · subst x
    have hy0 : y = 0 := by simpa using h.symm
    exact hy0.symm
  by_cases hy : y = 0
  · subst y
    simpa using h
  have hu : (Units.mk0 x hx) ^ 7 = (Units.mk0 y hy) ^ 7 := by
    apply Units.ext
    simpa using h
  exact congrArg (fun u : (ZMod ℓ)ˣ => (u : ZMod ℓ)) (hi hu)

/-- Ring subtraction gives the actual sextic as a seventh-power difference. -/
theorem centeredSevenSextic_cast_difference {R : Type*} [CommRing R] (D q : ℕ) :
    ((q : R) + D) ^ 7 - ((q : R) - D) ^ 7 =
      2 * (D : R) * (centeredSevenSextic D q : R) := by
  simp only [centeredSevenSextic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- A unit gap has nonzero sextic image at every odd seventh-power permutation prime. -/
theorem centeredSevenSextic_not_dvd_of_seven_power_permutation
    {ℓ D q : ℕ} (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hD : ¬ ℓ ∣ D) :
    ¬ ℓ ∣ centeredSevenSextic D q := by
  have : Fact (Nat.Prime ℓ) := ⟨hp⟩
  have hd : (D : ZMod ℓ) ≠ 0 := fun h => hD ((ZMod.natCast_eq_zero_iff D ℓ).mp h)
  have ht : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have hv := (ZMod.natCast_eq_zero_iff 2 ℓ).mp h
    have he := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hv
    rcases he with he | he
    · exact hp.ne_one he
    · exact hodd he
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (centeredSevenSextic D q) ℓ).mpr h
  have he := centeredSevenSextic_cast_difference (R := ZMod ℓ) D q
  rw [hz, mul_zero] at he
  have hxy := zmod_seventh_power_injective hp hcop (sub_eq_zero.mp he)
  have h2d : (2 : ZMod ℓ) * D = 0 := by linear_combination hxy
  exact (mul_ne_zero ht hd) h2d


/-- Complementary support excludes the same exact receiver; the fixed gap factor7
requires the explicit exclusion of modulus7. -/
theorem nestedAllocation_excluded_of_permutation_prime_support
    {ℓ M r : ℕ} (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hr : ¬ ℓ ∣ r) (hs : ℓ ∣ M / r) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) := by
  have hD : ¬ ℓ ∣ 7 ^ 27 * r ^ 49 := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · have hh := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow h)
      exact hh.elim hp.ne_one hnot7
    · exact hr (hp.dvd_of_dvd_pow h)
  intro h
  rcases (nestedAllocation_iff_centered M r).mp h with ⟨q, hq⟩
  have he : centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * (M / r) ^ 49 := by
    simpa only [← mul_assoc, show (64 : ℕ) * 7 = 448 by decide] using hq.2.1
  apply centeredSevenSextic_not_dvd_of_seven_power_permutation hp hodd hcop hD
  rw [he]
  exact dvd_mul_of_dvd_right (dvd_pow hs (by decide : 49 ≠ 0)) _

/-- Primitive allocation support lifts the permutation-prime obstruction to full sieves. -/
theorem sixthPowerSieved_smallCoefficient_permutation_prime_excluded
    {c ℓ n : ℕ} (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1)) (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * ℓ ^ n) := by
  rintro ⟨r, hmem, hprim, hsize, _, _, hbranch⟩
  have hs := eligible_smallCoefficient_prime_in_complement hp hc hn hmem hprim hsize
  apply nestedAllocation_excluded_of_permutation_prime_support hp hodd hnot7 hcop hs.1 hs.2
  exact hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)

end DkMath.FLT.Seven
