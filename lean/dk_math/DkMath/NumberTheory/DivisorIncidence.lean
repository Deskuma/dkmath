/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

#print "file: DkMath.NumberTheory.DivisorIncidence"

/-! Exact finite divisor incidence, multiple counts and factorial floor sums. -/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Prefix counting in the positive closed interval. -/
theorem card_Icc_filter_dvd (N d : ℕ) (_hd : 0 < d) :
    ((Finset.Icc 1 N).filter (d ∣ ·)).card = N / d := by
  have hi : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hi]
  exact Nat.Ioc_filter_dvd_card_eq_div N d

/-- Natural floor difference counts the multiples in an arbitrary positive shell. -/
theorem card_shell_filter_dvd {base top d : ℕ} (hbt : base ≤ top) (hd : 0 < d) :
    ((Finset.Icc (base + 1) top).filter (d ∣ ·)).card = top / d - base / d := by
  have hsub : (Finset.Icc 1 base).filter (d ∣ ·) ⊆
      (Finset.Icc 1 top).filter (d ∣ ·) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hk.1.1, hk.1.2.trans hbt⟩, hk.2⟩
  have he : (Finset.Icc (base + 1) top).filter (d ∣ ·) =
      (Finset.Icc 1 top).filter (d ∣ ·) \ (Finset.Icc 1 base).filter (d ∣ ·) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    omega
  rw [he, Finset.card_sdiff_of_subset hsub, card_Icc_filter_dvd top d hd,
    card_Icc_filter_dvd base d hd]

/-- Transpose a finite positive-shell/divisor incidence relation with any real weight. -/
theorem sum_shell_divisors_eq_floor {base top : ℕ} (hbt : base ≤ top) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc (base + 1) top, ∑ d ∈ m.divisors, f d) =
      ∑ d ∈ Finset.Icc 1 top, ((top / d - base / d : ℕ) : ℝ) * f d := by
  classical
  have hex : ∀ m ∈ Finset.Icc (base + 1) top,
      m.divisors = (Finset.Icc 1 top).filter (· ∣ m) := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hm0 : m ≠ 0 := by omega
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos h.1 (by omega)
      exact ⟨⟨hpos, (Nat.le_of_dvd (by omega) h.1).trans hm'.2⟩, h.1⟩
    · intro h; exact ⟨h.2, hm0⟩
  have hs : (∑ m ∈ Finset.Icc (base + 1) top, ∑ d ∈ m.divisors, f d) =
      ∑ m ∈ Finset.Icc (base + 1) top, ∑ d ∈ Finset.Icc 1 top,
        if d ∣ m then f d else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hex m hm, Finset.sum_filter]
  rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_shell_filter_dvd hbt (Finset.mem_Icc.mp hd).1]

/-- Pointwise von Mangoldt expansion plus exact incidence transposition. -/
theorem sum_shell_log_eq_floor {base top : ℕ} (hbt : base ≤ top) :
    (∑ m ∈ Finset.Icc (base + 1) top, Real.log (m : ℝ)) =
      ∑ d ∈ Finset.Icc 1 top,
        ((top / d - base / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  simpa only [ArithmeticFunction.vonMangoldt_sum] using
    sum_shell_divisors_eq_floor hbt ArithmeticFunction.vonMangoldt

/-- Multiplicative shell form; all factors in the positive interval are nonzero. -/
theorem log_shell_prod_eq_floor {base top : ℕ} (hbt : base ≤ top) :
    Real.log ((∏ m ∈ Finset.Icc (base + 1) top, m : ℕ) : ℝ) =
      ∑ d ∈ Finset.Icc 1 top,
        ((top / d - base / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  rw [Nat.cast_prod, Real.log_prod]
  · exact sum_shell_log_eq_floor hbt
  · intro m hm; exact_mod_cast (show m ≠ 0 by have h := Finset.mem_Icc.mp hm; omega)

/-- Generic factorial von Mangoldt floor identity, including the zero factorial. -/
theorem log_factorial_eq_floor (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  have hp : (∏ m ∈ Finset.Icc 1 N, m) = N.factorial := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact Finset.prod_Ico_id_eq_factorial N
  simpa only [Nat.zero_add, Nat.zero_div, Nat.sub_zero, hp] using
    (log_shell_prod_eq_floor (base := 0) (top := N) (Nat.zero_le N))

/-- Extending the factorial cutoff contributes only zero quotients. -/
theorem log_factorial_eq_floor_cutoff {N B : ℕ} (hNB : N ≤ B) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 B, ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  rw [log_factorial_eq_floor]
  apply Finset.sum_subset
  · intro d hd; exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans hNB⟩
  · intro d hd hnot
    have hNd : N < d := by
      have hd' := Finset.mem_Icc.mp hd
      simp only [Finset.mem_Icc, not_and] at hnot
      omega
    simp [Nat.div_eq_of_lt hNd]

end DkMath.NumberTheory
