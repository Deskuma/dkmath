import DkMath.Lib.NumberTheory.EisensteinLatticeLanding

/-! Kernel-checked diagnostics for the 2026-09-15 provider investigation.
    All coordinates are standard omega coordinates. No production API changes. -/

namespace ABCProviderDiagnostics

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.Lib.NumberTheory

local notation "N" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The literal unqualified existence question has a unit-root answer. -/
theorem unrestricted_factorization (a : ℕ) :
    ∃ beta gamma : TraceOneInt (-1),
      eisensteinCoord ((a : ℤ) + 2) 1 = beta * gamma ^ 2 := by
  exact ⟨eisensteinCoord ((a : ℤ) + 2) 1, 1, by simp⟩

/-- Full norm data identify a nonnegative cubic-family witness uniquely. -/
theorem cubic_norm_injective {a b : ℕ}
    (h : a ^ 2 + 3 * a + 3 = b ^ 2 + 3 * b + 3) : a = b := by
  nlinarith

/-- Equal norm does not force divisibility for a prescribed orientation. -/
theorem norm_divides_without_element_divides :
    N (eisensteinCoord 2 (-1)) ∣ N (eisensteinCoord 3 1) ∧
      ¬ eisensteinCoord 2 (-1) ∣ eisensteinCoord 3 1 := by
  constructor
  · norm_num [norm_eisensteinCoord]
  · intro h
    have hc := eisenstein_dvd_imp_norm_dvd_conjugate_coordinates h
    norm_num [norm_eisensteinCoord] at hc

/-- The first cubic value with a square factor is 343 at a=17.
    Its repeated modulus is 7^3, while both factor norms are 7. -/
theorem cubic_seventeen_factor :
    eisensteinCoord 3 2 * eisensteinCoord (-2) 1 ^ 2 =
      eisensteinCoord 19 1 := by
  rw [eisensteinCoord_mul_sq]
  norm_num

theorem cubic_seventeen_norms :
    N (eisensteinCoord 19 1) = 343 ∧
      N (eisensteinCoord 3 2) = 7 ∧ N (eisensteinCoord (-2) 1) = 7 := by
  norm_num [norm_eisensteinCoord]

/-- The conjugate candidate has exactly the required norm and fails to land. -/
theorem cubic_seventeen_wrong_square_orientation :
    N (eisensteinCoord (-3) (-1)) ^ 2 ∣ N (eisensteinCoord 19 1) ∧
      ¬ eisensteinCoord (-3) (-1) ^ 2 ∣ eisensteinCoord 19 1 := by
  constructor
  · norm_num [norm_eisensteinCoord]
  · intro h
    rw [eisensteinCoord_sq] at h
    have hc := eisenstein_dvd_imp_norm_dvd_conjugate_coordinates h
    norm_num [norm_eisensteinCoord] at hc

/-- The ramified residual is retained by beta at a=21. -/
theorem cubic_twenty_one_factor :
    eisensteinCoord 2 1 * eisensteinCoord (-3) 1 ^ 2 =
      eisensteinCoord 23 1 := by
  rw [eisensteinCoord_mul_sq]
  norm_num

/-- A general Eisenstein element can have square norm without a matching
    square divisor: N(7)=49, but no norm-7 element has square dividing 7. -/
theorem rational_seven_has_no_norm_seven_square_divisor (m n : ℤ)
    (hN : N (eisensteinCoord m n) = 7) :
    ¬ eisensteinCoord m n ^ 2 ∣ eisensteinCoord 7 0 := by
  intro h
  rw [norm_eisensteinCoord] at hN
  have hm : -3 ≤ m ∧ m ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (m - 2 * n)]
  have hn : -3 ≤ n ∧ n ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (2 * m - n)]
  rcases hm with ⟨hm₁, hm₂⟩
  rcases hn with ⟨hn₁, hn₂⟩
  rw [eisensteinCoord_sq] at h
  have hc := eisenstein_dvd_imp_norm_dvd_conjugate_coordinates h
  interval_cases m <;> interval_cases n <;> norm_num at hN
  all_goals norm_num [norm_eisensteinCoord] at hc

/-- Every square divisor of the scalar seven has unit root. Thus its square
    norm does not imply any nonunit element square factor. -/
theorem rational_seven_square_divisor_isUnit (m n : ℤ)
    (h : eisensteinCoord m n ^ 2 ∣ eisensteinCoord 7 0) :
    IsUnit (eisensteinCoord m n) := by
  have hd := traceOne_dvd_imp_norm_dvd_norm h
  have hd' : (N (eisensteinCoord m n)) ^ 2 ∣ (49 : ℤ) := by
    simpa [pow_two, traceOne_norm_mul, norm_eisensteinCoord] using hd
  set k := N (eisensteinCoord m n) with hk
  have hk0 : 0 ≤ k := by
    rw [hk, norm_eisensteinCoord]
    nlinarith [sq_nonneg (2 * m - n), sq_nonneg n]
  have hk7 : k ≤ 7 := by
    have hle := Int.le_of_dvd (by norm_num : 0 < (49 : ℤ)) hd'
    nlinarith
  have hkcases : k = 1 ∨ k = 7 := by
    interval_cases k <;> norm_num at hd'
    all_goals norm_num
  have hone : N (eisensteinCoord m n) = 1 := by
    rcases hkcases with h1 | h7
    · exact hk.symm.trans h1
    · exact False.elim (rational_seven_has_no_norm_seven_square_divisor m n
        (hk.symm.trans h7) h)
  rw [isUnit_iff_dvd_one]
  refine ⟨conj (eisensteinCoord m n), ?_⟩
  have hmul :=
    (traceOne_mul_conj (eisensteinCoord m n)).symm
  rw [hone] at hmul
  convert hmul using 1; ext <;> norm_num [DkMath.NumberTheory.TraceOneQuadratic.ofInt]

/-- A different element of exactly the same norm is itself a square. -/
theorem norm_forty_nine_square_contrast :
    N (eisensteinCoord 7 0) = N (eisensteinCoord 8 5) ∧
      eisensteinCoord (-3) (-1) ^ 2 = eisensteinCoord 8 5 := by
  constructor
  · norm_num [norm_eisensteinCoord]
  · rw [eisensteinCoord_sq]
    norm_num

end ABCProviderDiagnostics

#print axioms ABCProviderDiagnostics.unrestricted_factorization
#print axioms ABCProviderDiagnostics.cubic_norm_injective
#print axioms ABCProviderDiagnostics.norm_divides_without_element_divides
#print axioms ABCProviderDiagnostics.cubic_seventeen_factor
#print axioms ABCProviderDiagnostics.cubic_seventeen_norms
#print axioms ABCProviderDiagnostics.cubic_seventeen_wrong_square_orientation
#print axioms ABCProviderDiagnostics.cubic_twenty_one_factor
#print axioms ABCProviderDiagnostics.rational_seven_has_no_norm_seven_square_divisor
#print axioms ABCProviderDiagnostics.rational_seven_square_divisor_isUnit
#print axioms ABCProviderDiagnostics.norm_forty_nine_square_contrast
