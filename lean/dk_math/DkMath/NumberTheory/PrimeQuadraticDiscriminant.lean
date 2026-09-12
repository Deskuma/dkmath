/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.NumberTheory.PrimeQuadraticDiscriminant"

namespace DkMath.NumberTheory.PrimeQuadraticDiscriminant

open DkMath.NumberTheory.TraceOneQuadratic

/-! The signed prime discriminant attached to an odd prime. -/

/-- The canonical signed discriminant determined by the prime residue class modulo four. -/
def signedPrimeDiscriminant (p : ℕ) : ℤ :=
  if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

theorem signedPrimeDiscriminant_eq_or_neg (p : ℕ) :
    signedPrimeDiscriminant p = (p : ℤ) ∨
      signedPrimeDiscriminant p = -(p : ℤ) := by
  by_cases h : p % 4 = 1 <;> simp [signedPrimeDiscriminant, h]

theorem signedPrimeDiscriminant_natAbs (p : ℕ) :
    Int.natAbs (signedPrimeDiscriminant p) = p := by
  by_cases h : p % 4 = 1 <;> simp [signedPrimeDiscriminant, h]

theorem signedPrimeDiscriminant_mod_four
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    signedPrimeDiscriminant p % 4 = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hodd with ⟨k, hk⟩
    omega
  rcases hcases with h | h
  · rw [signedPrimeDiscriminant, if_pos h]
    exact_mod_cast h
  · have hpmod : (p : ℤ) % 4 = 3 := by
      exact_mod_cast h
    have hpnot : ¬(4 : ℤ) ∣ (p : ℤ) := by
      intro hdiv
      have hz : (p : ℤ) % 4 = 0 := Int.emod_eq_zero_of_dvd hdiv
      omega
    rw [signedPrimeDiscriminant, if_neg (by omega), Int.neg_emod]
    simp [hpnot, hpmod]

/-- The trace-one parameter having the signed prime discriminant. -/
def signedPrimeParameter (p : ℕ) : ℤ :=
  (signedPrimeDiscriminant p - 1) / 4

/-- The signed-prime trace-one parameter specializes to `-1` at `p = 3`. -/
theorem signedPrimeParameter_three :
    signedPrimeParameter 3 = -1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

theorem discr_signedPrimeParameter
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    discr (signedPrimeParameter p) = signedPrimeDiscriminant p := by
  have hmod := signedPrimeDiscriminant_mod_four hp hp2
  have hdecomp := Int.mul_ediv_add_emod (signedPrimeDiscriminant p - 1) 4
  simp only [signedPrimeParameter, discr]
  omega

end DkMath.NumberTheory.PrimeQuadraticDiscriminant
