/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.ABC.PadicValNat"

/-!
# Compatibility facade for generic `padicValNat` support

The reusable valuation lemmas are owned by
`DkMath.Lib.NumberTheory.PadicValNat`.  This module preserves the historical
`DkMath.ABC` names for existing ABC and research consumers without making the
lower library depend on ABC.
-/

namespace DkMath.ABC

lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 :=
  DkMath.Lib.NumberTheory.padicValNat_split p n

lemma padic_val_two_of_odd : ∀ n : ℕ, padicValNat 2 (2 * n + 1) = 0 :=
  DkMath.Lib.NumberTheory.padic_val_two_of_odd

lemma padic_val_two_of_even (n : ℕ) :
    (n = 0 → padicValNat 2 (2 * n) = 0 ∧ 1 + padicValNat 2 n = 1) ∧
    (n ≠ 0 → padicValNat 2 (2 * n) = 1 + padicValNat 2 n) :=
  DkMath.Lib.NumberTheory.padic_val_two_of_even n

lemma padicValNat_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    padicValNat p n = 0 ↔ ¬ p ∣ n :=
  DkMath.Lib.NumberTheory.padicValNat_eq_zero_iff hp hn

lemma padicValNat_le_self (n : ℕ) : padicValNat p n ≤ n :=
  DkMath.Lib.NumberTheory.padicValNat_le_self n

lemma padicValNat_le_log (p n : ℕ) (_hn : n ≠ 0) :
    padicValNat p n ≤ Nat.log p n :=
  DkMath.Lib.NumberTheory.padicValNat_le_log p n _hn

lemma Vp_ge_one_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    1 ≤ padicValNat p n ↔ p ∣ n :=
  DkMath.Lib.NumberTheory.Vp_ge_one_iff hp hn

lemma padicValNat_one_le_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hnz : n ≠ 0)
    (hpd : p ∣ n) : 1 ≤ padicValNat p n :=
  DkMath.Lib.NumberTheory.padicValNat_one_le_of_prime_dvd hp hnz hpd

lemma padicValNat_le_iff_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
    k ≤ padicValNat p n ↔ p ^ k ∣ n :=
  DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp hn k

lemma padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (_ha : a ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a :=
  DkMath.Lib.NumberTheory.padicValNat_pow hp d _ha

lemma padicValNat_pow' {p a : ℕ} (hp : p.Prime) (d : ℕ) (hpow : a ^ d ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a :=
  DkMath.Lib.NumberTheory.padicValNat_pow' hp d hpow

lemma dvd_padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (ha : a ≠ 0) :
    d ∣ padicValNat p (a ^ d) :=
  DkMath.Lib.NumberTheory.dvd_padicValNat_pow hp d ha

end DkMath.ABC
