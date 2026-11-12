/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Lib.NumberTheory.PrimeRatioOrder"

/-!
# Residue ratios and their multiplicative orders

[DkMath.Lib] GN-LIB-006a separates the finite-field/order kernel from the
Zsigmondy primitive-prime carrier. The historical namespace is retained for
compatibility, while the dependency direction is now Mathlib → Lib → owner.
Only the denominator is required nonzero in the power-difference equivalence;
a zero numerator has order zero. Positive order and the q-1 bound require
both coordinates nonzero. Characteristic two is included.
-/

namespace DkMath.NumberTheory.GapFocusing

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

The residue ratio in `ZMod q`. Arithmetic order statements assume `q` prime
and exclude a denominator divisible by `q`. -/
def primeRatio (q : ℕ) (a b : ℤ) : ZMod q :=
  (a : ZMod q) * (b : ZMod q)⁻¹

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

Multiplicative order of the residue ratio. -/
noncomputable def primeOrder (q : ℕ) (a b : ℤ) : ℕ := orderOf (primeRatio q a b)

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

Nonvanishing of a residue ratio follows from nonvanishing of both coordinates. -/
theorem primeRatio_ne_zero {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : primeRatio q a b ≠ 0 := by
  unfold primeRatio
  exact mul_ne_zero
    (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp h))
    (inv_ne_zero (fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).mp h)))

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

The scalar order agrees with the order in the unit group whenever both
coordinates are nonzero modulo the prime. -/
theorem primeOrder_eq_unit_order {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) :
    primeOrder q a b = orderOf (Units.mk0 (primeRatio q a b) (primeRatio_ne_zero ha hb)) := by
  simpa only [primeOrder, Units.val_mk0] using
    (orderOf_units (y := Units.mk0 (primeRatio q a b) (primeRatio_ne_zero ha hb)))

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

Divisibility of an integer power difference is exactly a multiplicative-order
condition. Only the denominator must be nonzero; a zero numerator has order zero. -/
theorem int_dvd_pow_sub_pow_iff_primeOrder_dvd {q : ℕ} [Fact q.Prime]
    (a b : ℤ) (n : ℕ) (hb : ¬ (q : ℤ) ∣ b) :
    (q : ℤ) ∣ a ^ n - b ^ n ↔ primeOrder q a b ∣ n := by
  have hb0 : (b : ZMod q) ≠ 0 :=
    fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).mp h)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow,
    Int.cast_pow, sub_eq_zero]
  unfold primeOrder primeRatio
  rw [orderOf_dvd_iff_pow_eq_one, mul_pow, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hb0)]

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

The natural-number formulation requires `b ≤ a` because subtraction is truncated. -/
theorem nat_dvd_pow_sub_pow_iff_primeOrder_dvd {q : ℕ} [Fact q.Prime]
    (a b n : ℕ) (hab : b ≤ a) (hb : ¬ q ∣ b) :
    q ∣ a ^ n - b ^ n ↔ primeOrder q a b ∣ n := by
  have hbZ : ¬ (q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have hcast : ((a ^ n - b ^ n : ℕ) : ℤ) = (a : ℤ) ^ n - (b : ℤ) ^ n := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hab n), Nat.cast_pow, Nat.cast_pow]
  rw [← Int.natCast_dvd_natCast, hcast]
  exact int_dvd_pow_sub_pow_iff_primeOrder_dvd a b n hbZ

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

For a nonzero ratio over a prime field, its order divides the size of the unit group. -/
theorem primeOrder_dvd_prime_sub_one {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : primeOrder q a b ∣ q - 1 :=
  ZMod.orderOf_dvd_card_sub_one (primeRatio_ne_zero ha hb)

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

Nonzero ratios have positive order, including characteristic two. -/
theorem primeOrder_pos {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : 0 < primeOrder q a b := by
  exact (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q - 1, Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt,
      ZMod.pow_card_sub_one_eq_one (primeRatio_ne_zero ha hb)⟩).orderOf_pos

/-- [DkMath.Lib] GN-LIB-006a: promoted from the general prefix of
`DkMath.NumberTheory.GapFocusing.PrimeOrder`; namespace and public type retained.
The primitive-prime-divisor carrier remains in the old application owner.

A prime cannot divide the order of a nonzero element of its prime field. -/
theorem primeOrder_coprime_prime {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : (primeOrder q a b).Coprime q := by
  have hq : q.Prime := Fact.out
  rw [Nat.coprime_comm]
  apply (hq.coprime_iff_not_dvd).2
  intro hdiv
  have hdivPred : q ∣ q - 1 := hdiv.trans (primeOrder_dvd_prime_sub_one ha hb)
  have hge : q ≤ q - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hdivPred
  exact (Nat.not_le_of_lt (Nat.sub_lt hq.pos Nat.zero_lt_one)) hge

end DkMath.NumberTheory.GapFocusing
