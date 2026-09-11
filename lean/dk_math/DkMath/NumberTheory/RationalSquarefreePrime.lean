/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.RationalSquarefreePrime"

namespace DkMath.NumberTheory.RationalSquarefreePrime

noncomputable section

/-- A rational whose square becomes integral after multiplication by a prime
is already an integer rational. -/
theorem rat_eq_int_of_prime_mul_sq
    {p : ℕ} (hp : p.Prime) (q : ℚ)
    (h : ∃ z : ℤ, (z : ℚ) = (p : ℚ) * q ^ 2) :
    ∃ a : ℤ, (a : ℚ) = q := by
  have hden : ((p : ℚ) * q ^ 2).den = 1 := by
    obtain ⟨z, hz⟩ := h
    rw [← hz]
    simp
  rw [pow_two] at hden
  rw [Rat.mul_den, Rat.mul_self_num, Rat.mul_self_den] at hden
  simp only [Rat.num_natCast, Rat.den_natCast, Int.natAbs_mul,
    Int.natAbs_natCast, Nat.one_mul] at hden
  have hden_eq : q.den * q.den =
      Nat.gcd (p * (q.num.natAbs * q.num.natAbs)) (q.den * q.den) := by
    symm
    apply Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_right _ _)
    simpa [Nat.mul_comm] using hden
  have hsq_dvd : q.den * q.den ∣
      p * (q.num.natAbs * q.num.natAbs) := by
    rw [hden_eq]
    exact Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime (q.den * q.den) (q.num.natAbs * q.num.natAbs) := by
    simpa [pow_two] using
      (Nat.Coprime.pow_left 2 (Nat.Coprime.pow_right 2 q.reduced.symm))
  have hden_dvd : q.den * q.den ∣ p :=
    (hcop.dvd_mul_left).mp (by simpa [Nat.mul_comm] using hsq_dvd)
  have hden_cases := (Nat.dvd_prime hp).mp hden_dvd
  rcases hden_cases with hden_one | hden_prime
  · refine ⟨q.num, ?_⟩
    have hden_one' : q.den = 1 := by
      apply Nat.eq_one_of_dvd_one
      rw [← hden_one]
      exact dvd_mul_right q.den q.den
    simpa [hden_one'] using (Rat.num_div_den q)
  · have hden_dvd_p : q.den ∣ p :=
      by rw [← hden_prime]; exact dvd_mul_right q.den q.den
    rcases (Nat.dvd_prime hp).mp hden_dvd_p with h | h
    · have : p = 1 := by simpa [h] using hden_prime.symm
      exact False.elim (hp.ne_one this)
    · have hbad : p * p = p := by simpa [h] using hden_prime
      exfalso
      nlinarith [hp.two_le]

/-- The same squarefree denominator argument for either signed prime. -/
theorem rat_eq_int_of_signedPrime_mul_sq
    {p : ℕ} (hp : p.Prime) {D : ℤ}
    (hD : D = (p : ℤ) ∨ D = -(p : ℤ)) (q : ℚ)
    (h : ∃ z : ℤ, (z : ℚ) = (D : ℚ) * q ^ 2) :
    ∃ a : ℤ, (a : ℚ) = q := by
  rcases hD with rfl | rfl
  · exact rat_eq_int_of_prime_mul_sq hp q h
  · obtain ⟨z, hz⟩ := h
    apply rat_eq_int_of_prime_mul_sq hp q
    refine ⟨-z, ?_⟩
    simpa [Int.cast_neg] using congrArg Neg.neg hz

end

end DkMath.NumberTheory.RationalSquarefreePrime
