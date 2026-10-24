/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Zsigmondy
import DkMath.Lib.NumberTheory.PrimeRatioOrder

#print "file: DkMath.NumberTheory.GapFocusing.PrimeOrder"

namespace DkMath.NumberTheory.GapFocusing

/-!
[DkMath.Lib] GN-LIB-006a: the two ratio/order definitions and seven general
theorems are now owned by `DkMath.Lib.NumberTheory.PrimeRatioOrder`.
The import preserves their names and types. Only the primitive-prime carrier
bridges below remain in this Zsigmondy-dependent owner.
-/

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
