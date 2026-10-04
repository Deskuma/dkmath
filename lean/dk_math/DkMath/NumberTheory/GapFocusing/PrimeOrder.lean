/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Zsigmondy
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.NumberTheory.GapFocusing.PrimeOrder"

namespace DkMath.NumberTheory.GapFocusing

/-- The residue ratio in `ZMod q`. Arithmetic order statements assume `q` prime
and exclude a denominator divisible by `q`. -/
def primeRatio (q : ℕ) (a b : ℤ) : ZMod q :=
  (a : ZMod q) * (b : ZMod q)⁻¹

/-- Multiplicative order of the residue ratio. -/
noncomputable def primeOrder (q : ℕ) (a b : ℤ) : ℕ := orderOf (primeRatio q a b)

/-- Nonvanishing of a residue ratio follows from nonvanishing of both coordinates. -/
theorem primeRatio_ne_zero {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : primeRatio q a b ≠ 0 := by
  unfold primeRatio
  exact mul_ne_zero
    (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp h))
    (inv_ne_zero (fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).mp h)))

/-- The scalar order agrees with the order in the unit group whenever both
coordinates are nonzero modulo the prime. -/
theorem primeOrder_eq_unit_order {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) :
    primeOrder q a b = orderOf (Units.mk0 (primeRatio q a b) (primeRatio_ne_zero ha hb)) := by
  simpa only [primeOrder, Units.val_mk0] using
    (orderOf_units (y := Units.mk0 (primeRatio q a b) (primeRatio_ne_zero ha hb)))

/-- Divisibility of an integer power difference is exactly a multiplicative-order
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

/-- The natural-number formulation requires `b ≤ a` because subtraction is truncated. -/
theorem nat_dvd_pow_sub_pow_iff_primeOrder_dvd {q : ℕ} [Fact q.Prime]
    (a b n : ℕ) (hab : b ≤ a) (hb : ¬ q ∣ b) :
    q ∣ a ^ n - b ^ n ↔ primeOrder q a b ∣ n := by
  have hbZ : ¬ (q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have hcast : ((a ^ n - b ^ n : ℕ) : ℤ) = (a : ℤ) ^ n - (b : ℤ) ^ n := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hab n), Nat.cast_pow, Nat.cast_pow]
  rw [← Int.natCast_dvd_natCast, hcast]
  exact int_dvd_pow_sub_pow_iff_primeOrder_dvd a b n hbZ

/-- For a nonzero ratio over a prime field, its order divides the size of the unit group. -/
theorem primeOrder_dvd_prime_sub_one {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : primeOrder q a b ∣ q - 1 :=
  ZMod.orderOf_dvd_card_sub_one (primeRatio_ne_zero ha hb)

/-- Nonzero ratios have positive order, including characteristic two. -/
theorem primeOrder_pos {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : 0 < primeOrder q a b := by
  exact (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q - 1, Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt,
      ZMod.pow_card_sub_one_eq_one (primeRatio_ne_zero ha hb)⟩).orderOf_pos

/-- A prime cannot divide the order of a nonzero element of its prime field. -/
theorem primeOrder_coprime_prime {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : (primeOrder q a b).Coprime q := by
  have hq : q.Prime := Fact.out
  rw [Nat.coprime_comm]
  apply (hq.coprime_iff_not_dvd).2
  intro hdiv
  have hdivPred : q ∣ q - 1 := hdiv.trans (primeOrder_dvd_prime_sub_one ha hb)
  have hge : q ≤ q - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hdivPred
  exact (Nat.not_le_of_lt (Nat.sub_lt hq.pos Nat.zero_lt_one)) hge

/-- At a degree above one, a primitive prime cannot divide either coordinate.
No coordinate coprimality assumption is needed for this consequence. -/
theorem primitivePrimeDivisor_not_dvd_coordinates {a b n q : ℕ}
    (hab : b ≤ a) (hn : 1 < n)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q) :
    ¬ q ∣ a ∧ ¬ q ∣ b := by
  have hq : q.Prime := hprim.prime
  have hlow : ¬ q ∣ a - b := by
    simpa using hprim.not_dvd_lower Nat.zero_lt_one hn
  have hpowle : b ^ n ≤ a ^ n := Nat.pow_le_pow_left hab n
  have hb : ¬ q ∣ b := by
    intro hqb
    have hqbpow : q ∣ b ^ n := dvd_pow hqb (by omega)
    have hqapow : q ∣ a ^ n := by
      rw [← Nat.sub_add_cancel hpowle]
      exact Nat.dvd_add hprim.dvd hqbpow
    have hqa : q ∣ a := hq.dvd_of_dvd_pow hqapow
    exact hlow (Nat.dvd_sub hqa hqb)
  refine ⟨?_, hb⟩
  intro hqa
  have hqapow : q ∣ a ^ n := dvd_pow hqa (by omega)
  have hqbpow : q ∣ b ^ n := by
    have hsub : q ∣ a ^ n - (a ^ n - b ^ n) := Nat.dvd_sub hqapow hprim.dvd
    simpa [Nat.sub_sub_self hpowle] using hsub
  exact hb (hq.dvd_of_dvd_pow hqbpow)

/-- The existing primitive-prime notion is exactly order equal to the positive degree,
under the hypotheses needed to interpret the natural power difference modulo `q`. -/
theorem primitivePrimeDivisor_iff_primeOrder_eq {q a b n : ℕ} [Fact q.Prime]
    (hab : b ≤ a) (hn : 0 < n) (hb : ¬ q ∣ b) :
    DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q ↔ primeOrder q a b = n := by
  rw [DkMath.Zsigmondy.PrimitivePrimeDivisor, and_iff_right (Fact.out : q.Prime)]
  rw [primeOrder, orderOf_eq_iff hn]
  constructor
  · rintro ⟨hdiv, hlower⟩
    refine ⟨?_, fun m hm hnpos => ?_⟩
    · exact orderOf_dvd_iff_pow_eq_one.mp
        ((nat_dvd_pow_sub_pow_iff_primeOrder_dvd a b n hab hb).mp hdiv)
    · intro hpow
      exact hlower m hnpos hm
        ((nat_dvd_pow_sub_pow_iff_primeOrder_dvd a b m hab hb).mpr
          (orderOf_dvd_iff_pow_eq_one.mpr hpow))
  · rintro ⟨hpow, hlower⟩
    refine ⟨?_, fun m hmpos hm => ?_⟩
    · exact (nat_dvd_pow_sub_pow_iff_primeOrder_dvd a b n hab hb).mpr
        (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    · intro hdiv
      exact hlower m hm hmpos
        (orderOf_dvd_iff_pow_eq_one.mp
          ((nat_dvd_pow_sub_pow_iff_primeOrder_dvd a b m hab hb).mp hdiv))

/-- Above degree one, primitiveness can itself supply the denominator hypothesis.
This form includes every prime with `b ≤ a`, without coordinate coprimality. -/
theorem primitivePrimeDivisor_iff_primeOrder_eq_and_not_dvd {q a b n : ℕ}
    [Fact q.Prime] (hab : b ≤ a) (hn : 1 < n) :
    DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q ↔
      primeOrder q a b = n ∧ ¬ q ∣ b := by
  constructor
  · intro hprim
    have hb := (primitivePrimeDivisor_not_dvd_coordinates hab hn hprim).2
    exact ⟨(primitivePrimeDivisor_iff_primeOrder_eq hab (by omega) hb).mp hprim, hb⟩
  · rintro ⟨hord, hb⟩
    exact (primitivePrimeDivisor_iff_primeOrder_eq hab (by omega) hb).mpr hord

/-- A primitive prime at degree above one is congruent to one modulo that degree. -/
theorem primitivePrimeDivisor_degree_dvd_prime_sub_one {q a b n : ℕ}
    (hab : b ≤ a) (hn : 1 < n)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q) : n ∣ q - 1 := by
  let : Fact q.Prime := ⟨hprim.prime⟩
  obtain ⟨ha, hb⟩ := primitivePrimeDivisor_not_dvd_coordinates hab hn hprim
  have haZ : ¬ (q : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha
  have hbZ : ¬ (q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have hord := (primitivePrimeDivisor_iff_primeOrder_eq hab (by omega) hb).mp hprim
  simpa [hord] using primeOrder_dvd_prime_sub_one haZ hbZ

end DkMath.NumberTheory.GapFocusing
