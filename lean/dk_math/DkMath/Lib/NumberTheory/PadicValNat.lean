/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.PadicValNat"

/-!
# Generic `padicValNat` support

This lower-layer module contains reusable natural-number valuation utilities.
It is independent of ABC, FLT, RH, and other research packages.  The former
`DkMath.ABC.PadicValNat` path remains as a compatibility facade.
-/

namespace DkMath.Lib.NumberTheory

/-- Decompose a natural-number p-adic valuation into its first layer and remainder. -/
lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 := by
  by_cases h : padicValNat p n = 0
  · simp [h]
  · by_cases h1 : padicValNat p n = 1
    · simp [h1]
    · have : padicValNat p n ≥ 2 := by omega
      have : min (padicValNat p n) 1 = 1 := by omega
      have : max (padicValNat p n - 1) 0 = padicValNat p n - 1 := by omega
      omega

/-! ### Basic p-adic valuation counting lemmas -/

/-- The 2-adic valuation of every odd number `2 * n + 1` is zero. -/
lemma padic_val_two_of_odd : ∀ n : ℕ, padicValNat 2 (2 * n + 1) = 0 := fun n => by
  apply padicValNat.eq_zero_of_not_dvd
  omega

/-- The standard zero/nonzero split for the valuation of `2 * n`. -/
lemma padic_val_two_of_even (n : ℕ) :
    (n = 0 → padicValNat 2 (2 * n) = 0 ∧ 1 + padicValNat 2 n = 1) ∧
    (n ≠ 0 → padicValNat 2 (2 * n) = 1 + padicValNat 2 n) := by
  constructor
  · intro h
    rw [h, Nat.mul_zero, padicValNat_zero_right, Nat.add_zero]
    exact ⟨rfl, rfl⟩
  · intro h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) h
    rw [padicValNat.mul (by norm_num) h]
    simp

/-! ### Basic bounds on p-adic valuation -/

/-- For a prime `p`, `padicValNat p n = 0` exactly when `p` does not divide nonzero `n`. -/
lemma padicValNat_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    padicValNat p n = 0 ↔ ¬ p ∣ n := by
  rw [padicValNat.eq_zero_iff]
  simp only [hp.ne_one, false_or]
  simp only [hn, false_or]

/-- The p-adic valuation of `n` is at most `n`. -/
lemma padicValNat_le_self (n : ℕ) : padicValNat p n ≤ n := by
  cases n with
  | zero => simp [padicValNat_zero_right]
  | succ n =>
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    calc padicValNat p (n + 1)
      _ ≤ Nat.log p (n + 1) := padicValNat_le_nat_log (n + 1)
      _ ≤ n + 1 := Nat.log_le_self _ _

/-- The standard logarithmic upper bound for `padicValNat`. -/
lemma padicValNat_le_log (p n : ℕ) (_hn : n ≠ 0) :
    padicValNat p n ≤ Nat.log p n := by
  exact padicValNat_le_nat_log n

/-- For a prime `p` and nonzero `n`, one valuation layer is equivalent to `p ∣ n`. -/
lemma Vp_ge_one_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    1 ≤ padicValNat p n ↔ p ∣ n := by
  have h1 : (padicValNat p n ≥ 1) ↔ (padicValNat p n ≠ 0) := by
    simp [ge_iff_le, Nat.one_le_iff_ne_zero]
  have h0 := padicValNat_eq_zero_iff hp hn
  have h2 : (padicValNat p n ≠ 0) ↔ (p ∣ n) := by
    refine Iff.intro ?mp ?mpr
    · intro hnz
      by_contra hnp
      have : padicValNat p n = 0 := h0.mpr hnp
      contradiction
    · intro hpd
      by_contra hnz
      have : ¬ p ∣ n := h0.mp hnz
      contradiction
  exact Iff.trans h1 h2

/-- A prime divisor gives at least one p-adic valuation layer. -/
lemma padicValNat_one_le_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hnz : n ≠ 0)
    (hpd : p ∣ n) : 1 ≤ padicValNat p n := by
  have hge := Vp_ge_one_iff hp hnz
  exact hge.mpr hpd

/-- Convert a valuation lower bound into divisibility by the corresponding power. -/
lemma padicValNat_le_iff_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
    k ≤ padicValNat p n ↔ p ^ k ∣ n := by
  exact Iff.symm (@padicValNat_dvd_iff_le p (Fact.mk hp) n k hn)

/-! ### p-adic valuation of powers -/

/-- The valuation of a nonzero power is the exponent times the valuation of its base. -/
lemma padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (_ha : a ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact padicValNat.pow a d

/-- A power valuation identity using nonzeroness of the power as the input hypothesis. -/
lemma padicValNat_pow' {p a : ℕ} (hp : p.Prime) (d : ℕ) (hpow : a ^ d ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a := by
  by_cases hd : d = 0
  · subst hd
    simp [padicValNat_one_right]
  · have ha : a ≠ 0 := by
      intro ha_eq
      rw [ha_eq, zero_pow hd] at hpow
      exact hpow rfl
    exact padicValNat_pow hp d ha

/-- The exponent divides the valuation of a nonzero power. -/
lemma dvd_padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (ha : a ≠ 0) :
    d ∣ padicValNat p (a ^ d) := by
  rw [padicValNat_pow hp d ha]
  exact dvd_mul_right d _

end DkMath.Lib.NumberTheory
