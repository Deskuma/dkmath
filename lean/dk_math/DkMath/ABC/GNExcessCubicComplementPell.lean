/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicComplement

#print "file: DkMath.ABC.GNExcessCubicComplement"

/-!
# Pell family for the canonical cubic complement

This module freezes an explicit infinite family satisfying
`a^2 + 3*a + 3 = 3*d^2`.  Its canonical complement is exactly `3` at every
member.  The family is a structural obstruction to any argument that bounds
the number of points solely from the smallness of the complement.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-- Discriminant identity for the canonical quadratic. -/
theorem cubicQuadratic_discriminant_identity (a : ℕ) :
    4 * (a ^ 2 + 3 * a + 3) = (2 * a + 3) ^ 2 + 3 := by
  ring

/-- The canonical quadratic lies strictly between two consecutive squares. -/
theorem cubicQuadratic_ne_square (a d : ℕ) :
    a ^ 2 + 3 * a + 3 ≠ d ^ 2 := by
  intro he
  have hl : a + 1 < d := by nlinarith
  have hu : d < a + 2 := by nlinarith
  omega

/-- If `3 ∤ d`, the full repeated part of `3*d^2` is `d^2`. -/
private theorem repeatedPrimePowerPart_factorization_at (n q : ℕ) :
    (repeatedPrimePowerPart n).factorization q =
      if 2 ≤ n.factorization q then n.factorization q else 0 := by
  rw [repeatedPrimePowerPart_factorization]
  by_cases h : 2 ≤ n.factorization q
  · have hs : q ∈ n.factorization.support :=
      Finsupp.mem_support_iff.mpr (by omega)
    rw [if_pos ⟨hs, h⟩, if_pos h]
  · simp only [h, and_false, if_false]

theorem repeatedPrimePowerPart_three_mul_sq {d : ℕ}
    (hd : d ≠ 0) (h3 : ¬ 3 ∣ d) :
    repeatedPrimePowerPart (3 * d ^ 2) = d ^ 2 := by
  apply Nat.eq_of_factorization_eq
    (repeatedPrimePowerPart_pos _).ne' (pow_ne_zero _ hd)
  intro q
  rw [repeatedPrimePowerPart_factorization_at,
    Nat.factorization_mul (by decide) (pow_ne_zero _ hd),
    Nat.factorization_pow, Nat.prime_three.factorization]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hq : 3 = q
  · subst q
    rw [Nat.factorization_eq_zero_of_not_dvd h3]
    norm_num
  · rw [if_neg hq]
    by_cases hv : d.factorization q = 0
    · rw [hv]
      norm_num
    · have htwo : 2 ≤ 0 + 2 * d.factorization q := by omega
      rw [if_pos htwo]
      omega

/-- The canonical repeated part is `d^2` whenever the quadratic equals
`3*d^2` with `3 ∤ d`. -/
theorem GNNonExceptionalRepeatedPart_three_one_eq_sq_of_quadratic_eq_three_sq
    {a d : ℕ} (h : a ^ 2 + 3 * a + 3 = 3 * d ^ 2)
    (hd : d ≠ 0) (h3 : ¬ 3 ∣ d) :
    GNNonExceptionalRepeatedPart 3 a 1 = d ^ 2 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  simp only [mul_one, one_pow]
  rw [h]
  exact repeatedPrimePowerPart_three_mul_sq hd h3

/-- The Pell-type canonical cubic recurrence. -/
def GNCubicComplementPell : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
      let (a, d) := GNCubicComplementPell n
      (7 * a + 12 * d + 9, 4 * a + 7 * d + 6)

private theorem GNCubicComplementPell_step
    {a d : ℕ} (h : a ^ 2 + 3 * a + 3 = 3 * d ^ 2) :
    (7 * a + 12 * d + 9) ^ 2 + 3 * (7 * a + 12 * d + 9) + 3 =
      3 * (4 * a + 7 * d + 6) ^ 2 := by
  nlinarith

private theorem GNCubicComplementPell_step_grows (a d : ℕ) :
    a < 7 * a + 12 * d + 9 := by omega

/-- Every Pell pair satisfies the quadratic identity and its residue guards. -/
theorem GNCubicComplementPell_invariant (n : ℕ) :
    (GNCubicComplementPell n).1 ^ 2 +
        3 * (GNCubicComplementPell n).1 + 3 =
      3 * (GNCubicComplementPell n).2 ^ 2 ∧
    (GNCubicComplementPell n).1 % 3 = 0 ∧
    (GNCubicComplementPell n).2 % 3 = 1 := by
  induction n with
  | zero => norm_num [GNCubicComplementPell]
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [GNCubicComplementPell] using
        GNCubicComplementPell_step ih.1
    · change (7 * (GNCubicComplementPell n).1 +
        12 * (GNCubicComplementPell n).2 + 9) % 3 = 0
      omega
    · change (4 * (GNCubicComplementPell n).1 +
        7 * (GNCubicComplementPell n).2 + 6) % 3 = 1
      omega

/-- The repeated part along the Pell family is exactly the square coordinate. -/
theorem GNCubicComplementPell_repeatedPart (n : ℕ) :
    GNNonExceptionalRepeatedPart 3 (GNCubicComplementPell n).1 1 =
      (GNCubicComplementPell n).2 ^ 2 := by
  have hi := GNCubicComplementPell_invariant n
  apply GNNonExceptionalRepeatedPart_three_one_eq_sq_of_quadratic_eq_three_sq
    hi.1
  · have : 0 < (GNCubicComplementPell n).2 := by
      induction n with
      | zero => norm_num [GNCubicComplementPell]
      | succ n ih =>
          simp only [GNCubicComplementPell]
          omega
    omega
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega

/-- Every Pell point has canonical complement exactly `3`. -/
theorem GNCubicComplementPell_complement_eq_three (n : ℕ) :
    GNExcessCubicComplement (GNCubicComplementPell n).1 = 3 := by
  have hi := GNCubicComplementPell_invariant n
  have hd : 0 < (GNCubicComplementPell n).2 ^ 2 := by
    have hp : 0 < (GNCubicComplementPell n).2 := by
      induction n with
      | zero => norm_num [GNCubicComplementPell]
      | succ n ih =>
          simp only [GNCubicComplementPell]
          omega
    positivity
  unfold GNExcessCubicComplement
  rw [GNCubicComplementPell_repeatedPart, GN_three_dual_explicit]
  simp only [mul_one, one_pow]
  rw [hi.1, Nat.mul_div_cancel _ hd]

/-- The witness coordinate of the Pell family is strictly increasing. -/
theorem GNCubicComplementPell_strictMono :
    StrictMono (fun n => (GNCubicComplementPell n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (GNCubicComplementPell n).1 <
    7 * (GNCubicComplementPell n).1 +
      12 * (GNCubicComplementPell n).2 + 9
  exact GNCubicComplementPell_step_grows _ _

private theorem GNCubicComplementPell_index_le (n : ℕ) :
    n ≤ (GNCubicComplementPell n).1 := by
  induction n with
  | zero => norm_num [GNCubicComplementPell]
  | succ n ih =>
      simp [GNCubicComplementPell]
      omega

/-- Arbitrarily large canonical witnesses have complement `3`. -/
theorem exists_large_cubic_point_complement_eq_three (B : ℕ) :
    ∃ a : ℕ, B < a ∧ GNExcessCubicComplement a = 3 := by
  refine ⟨(GNCubicComplementPell (B + 1)).1, ?_,
    GNCubicComplementPell_complement_eq_three (B + 1)⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self B)
    (GNCubicComplementPell_index_le (B + 1))

/-- Exact paired identities retained for future orientation work. -/
theorem cubicOrientation_product_identity_one (a : ℕ) :
    (a ^ 2 + 3 * a + 3) * (3 * a ^ 2 + 3 * a + 1) =
      3 * (a + 1) ^ 4 + a ^ 2 := by ring

theorem cubicOrientation_linear_difference_one (a : ℤ) :
    3 * (a ^ 2 + 3 * a + 3) - (3 * a ^ 2 + 3 * a + 1) =
      6 * a + 8 := by ring

end DkMath.ABC
