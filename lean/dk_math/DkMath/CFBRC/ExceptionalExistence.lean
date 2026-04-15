/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.CFBRC.Bridge
import DkMath.NumberTheory.Gcd.GN
import Mathlib

/-! # CFBRC Exceptional Existence

`d | x` (exceptional / BranchA case) のもとで
`cyclotomicPrimeCore d x u` に `x` を割らない素因子が存在することを示す。

## 証明概略

1. `gcd(GN, x) = d`: gcd_gap_GN_dvd_exp + d | GN で sandwich
2. `d ∤ (GN/d)`: GN ≡ d*u^{d-1} (mod d²) かつ Coprime(u,d)
3. `GN/d > 1`: core > d * u^{d-1}
4. ∃ q prime, q | GN, q ≠ d, q ∤ x
-/

namespace DkMath.CFBRC

open scoped BigOperators
open DkMath.CosmicFormulaBinom

section GCDLemmas

variable {d x u : ℕ}

/-- d | GN when d | x. -/
theorem prime_dvd_GN_of_dvd_gap (_hd : Nat.Prime d) (hdx : d ∣ x) :
    d ∣ GN d x u := by
  rw [GN_eq_sum]
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  by_cases hk0 : k = 0
  · subst hk0; simp [Nat.choose_one_right]
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow hdx (by omega)) _) _

/-- gcd(GN, x) = d when d prime, d | x, Coprime x u. -/
theorem gcd_GN_eq_prime (hd : Nat.Prime d) (hx : 0 < x) (_hu : 0 < u)
    (hcop : Nat.Coprime x u) (hdx : d ∣ x) :
    Nat.gcd (GN d x u) x = d := by
  have hcop_add : Nat.Coprime (x + u) u := by
    exact (Nat.coprime_add_self_left.mpr hcop)
  have hyz : u < x + u := by omega
  have hgcd_dvd_d : Nat.gcd x (GN d x u) ∣ d := by
    simpa [Nat.add_sub_cancel_left] using
      DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
        (p := d) (z := x + u) (y := u) (Nat.one_le_of_lt hd.one_lt) hyz hcop_add
  have hd_dvd_gcd : d ∣ Nat.gcd x (GN d x u) :=
    Nat.dvd_gcd hdx (prime_dvd_GN_of_dvd_gap hd hdx)
  rw [Nat.gcd_comm]
  exact Nat.dvd_antisymm hgcd_dvd_d hd_dvd_gcd

end GCDLemmas

section ModLemmas

variable {d x u : ℕ}

/-- Each k ≥ 1 term in GN_eq_sum is divisible by d² when d prime ≥ 5, d | x. -/
private lemma GN_tail_term_dvd_sq (hd : Nat.Prime d) (hd5 : 5 ≤ d) (hdx : d ∣ x)
    {k : ℕ} (hk1 : 1 ≤ k) (hkd : k < d) :
    d ^ 2 ∣ Nat.choose d (k + 1) * x ^ k * u ^ (d - 1 - k) := by
  have hd_dvd_xk : d ∣ x ^ k := dvd_pow hdx (by omega)
  by_cases hk_lt : k + 1 < d
  · -- d | C(d,k+1) and d | x^k → d² | their product
    have hdc : d ∣ Nat.choose d (k + 1) := hd.dvd_choose_self (by omega) hk_lt
    have : d ^ 2 ∣ Nat.choose d (k + 1) * x ^ k := by
      rw [sq]; exact Nat.mul_dvd_mul hdc hd_dvd_xk
    exact dvd_mul_of_dvd_left this _
  · -- k+1 = d → k = d-1, so C(d,d) = 1 and d² | x^{d-1} (since d ≥ 5 → d-1 ≥ 2)
    have hk_eq : k = d - 1 := by omega
    subst hk_eq
    have : d ^ 2 ∣ x ^ (d - 1) := by
      have h2 : 2 ≤ d - 1 := by omega
      calc d ^ 2 ∣ x ^ 2 := by rw [sq, sq]; exact Nat.mul_dvd_mul hdx hdx
        _ ∣ x ^ (d - 1) := Nat.pow_dvd_pow x h2
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _

/-- GN ≡ d * u^{d-1} (mod d²). -/
theorem GN_congr_mul_pow_mod_sq (hd : Nat.Prime d) (hd5 : 5 ≤ d) (hdx : d ∣ x) :
    GN d x u ≡ d * u ^ (d - 1) [MOD d ^ 2] := by
  rw [GN_eq_sum]
  -- Split: range d = {0} ∪ Ico 1 d
  have hsplit : Finset.range d = insert 0 (Finset.Ico 1 d) := by
    ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
  have hdisj : 0 ∉ Finset.Ico 1 d := by simp
  rw [hsplit, Finset.sum_insert hdisj]
  simp only [Nat.cast_id]
  -- k=0 term = d * u^{d-1}
  conv_lhs => rw [show Nat.choose d (0 + 1) * x ^ 0 * u ^ (d - 1 - 0) = d * u ^ (d - 1) from
    by simp [Nat.choose_one_right]]
  -- Suffices: d² | tail
  have htail : d ^ 2 ∣ ∑ k ∈ Finset.Ico 1 d,
      Nat.choose d (k + 1) * x ^ k * u ^ (d - 1 - k) :=
    Finset.dvd_sum fun k hk => by
      rw [Finset.mem_Ico] at hk
      exact GN_tail_term_dvd_sq hd hd5 hdx hk.1 hk.2
  -- a + tail ≡ a (mod d²) when d² | tail
  change d * u ^ (d - 1) + _ ≡ d * u ^ (d - 1) [MOD d ^ 2]
  exact (Nat.modEq_zero_iff_dvd.mpr htail).add_left _

/-- d ∤ (GN/d). -/
theorem not_prime_dvd_GN_div_prime (hd : Nat.Prime d) (hd5 : 5 ≤ d)
    (_hx : 0 < x) (_hu : 0 < u)
    (hcop : Nat.Coprime x u) (hdx : d ∣ x) :
    ¬ d ∣ (GN d x u / d) := by
  have hd_dvd_GN : d ∣ GN d x u := prime_dvd_GN_of_dvd_gap hd hdx
  intro h
  -- d | GN/d → d² | GN
  have hd2 : d ^ 2 ∣ GN d x u := by
    rw [(Nat.mul_div_cancel' hd_dvd_GN).symm, sq]
    exact Nat.mul_dvd_mul_left d h
  -- GN ≡ d*u^{d-1} mod d²
  have hmod : GN d x u ≡ d * u ^ (d - 1) [MOD d ^ 2] := GN_congr_mul_pow_mod_sq hd hd5 hdx
  -- d² | GN → GN % d² = 0
  have hGN_mod : GN d x u % (d ^ 2) = 0 := Nat.mod_eq_zero_of_dvd hd2
  -- ModEq: GN % d² = (d*u^{d-1}) % d² → (d*u^{d-1}) % d² = 0
  have hduq_mod : d * u ^ (d - 1) % (d ^ 2) = 0 := by
    rwa [← hmod]
  -- d² | d*u^{d-1}
  have hd2_duq : d ^ 2 ∣ d * u ^ (d - 1) := Nat.dvd_of_mod_eq_zero hduq_mod
  -- d² | d*u^{d-1} → d | u^{d-1}
  have hdu : d ∣ u ^ (d - 1) := by
    rw [sq] at hd2_duq
    exact (Nat.mul_dvd_mul_iff_left hd.pos).mp hd2_duq
  -- Coprime(u, d) → d ∤ u^{d-1}, contradiction
  have hcop_ud : Nat.Coprime u d := Nat.Coprime.coprime_dvd_right hdx hcop.symm
  have hcop_pow : Nat.Coprime (u ^ (d - 1)) d := hcop_ud.pow_left _
  -- gcd(u^{d-1}, d) = 1 but d | u^{d-1} → d | 1 → d ≤ 1 → contradiction
  have hd_le : d ≤ 1 := Nat.le_of_dvd (by omega) (hcop_pow ▸ Nat.dvd_gcd hdu dvd_rfl)
  omega

end ModLemmas

section SizeLemmas

variable {d x u : ℕ}

/-- core > d * u^{d-1}. -/
theorem cyclotomicPrimeCore_gt_mul_pow (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    d * u ^ (d - 1) < cyclotomicPrimeCore d x u := by
  rw [cyclotomicPrimeCore, show d * u ^ (d - 1) = ∑ _ ∈ Finset.range d, u ^ (d - 1) from by
    simp [Finset.sum_const, Finset.card_range]]
  apply Finset.sum_lt_sum
  · intro k hk
    rw [Finset.mem_range] at hk
    calc u ^ (d - 1)
        = u ^ k * u ^ (d - 1 - k) := by rw [← pow_add]; congr 1; omega
      _ ≤ (x + u) ^ k * u ^ (d - 1 - k) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_add_left u x) k)
  · exact ⟨1, Finset.mem_range.mpr (by omega), by
      change u ^ (d - 1) < (x + u) ^ 1 * u ^ (d - 1 - 1)
      rw [pow_one]
      calc u ^ (d - 1)
          = u ^ ((d - 1 - 1) + 1) := by congr 1; omega
        _ = u ^ (d - 1 - 1) * u := pow_succ u _
        _ = u * u ^ (d - 1 - 1) := Nat.mul_comm _ _
        _ < (x + u) * u ^ (d - 1 - 1) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero (by positivity))⟩

/-- GN/d > 1. -/
theorem GN_div_prime_gt_one (hd : Nat.Prime d) (hd5 : 5 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hdx : d ∣ x) :
    1 < GN d x u / d := by
  have hd_dvd : d ∣ GN d x u := prime_dvd_GN_of_dvd_gap hd hdx
  have hgt := cyclotomicPrimeCore_gt_mul_pow (by omega : 2 ≤ d) hx hu
  rw [cyclotomicPrimeCore_eq_GN_nat hx] at hgt
  have hmul : GN d x u = d * (GN d x u / d) := (Nat.mul_div_cancel' hd_dvd).symm
  have : d * u ^ (d - 1) < d * (GN d x u / d) := hmul ▸ hgt
  have : u ^ (d - 1) < GN d x u / d := Nat.lt_of_mul_lt_mul_left this
  calc 1 ≤ u ^ (d - 1) := Nat.one_le_pow _ _ hu
    _ < GN d x u / d := this

end SizeLemmas

/-! ## Main theorem -/

theorem exists_prime_factor_cyclotomicPrimeCore_not_dvd_gap_exceptional
    {d x u : ℕ} (hd : Nat.Prime d) (hd5 : 5 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hdx : d ∣ x)
    (_hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x := by
  rw [cyclotomicPrimeCore_eq_GN_nat hx]
  have hgcd := gcd_GN_eq_prime hd hx hu hcop hdx
  have hd_not := not_prime_dvd_GN_div_prime hd hd5 hx hu hcop hdx
  have hgt := GN_div_prime_gt_one hd hd5 hx hu hdx
  have hm_ne : GN d x u / d ≠ 1 := by omega
  obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hm_ne
  have hne : q ≠ d := fun h => hd_not (h ▸ hqd)
  have hd_dvd : d ∣ GN d x u := prime_dvd_GN_of_dvd_gap hd hdx
  have hqGN : q ∣ GN d x u := hqd.trans (Nat.div_dvd_of_dvd hd_dvd)
  have hqnx : ¬ q ∣ x := by
    intro hqx
    have hq_dvd_gcd : q ∣ Nat.gcd (GN d x u) x := Nat.dvd_gcd hqGN hqx
    rw [hgcd] at hq_dvd_gcd
    exact hne (hd.eq_one_or_self_of_dvd q hq_dvd_gcd |>.resolve_left hqp.one_lt.ne')
  exact ⟨q, hqp, hqGN, hqnx⟩

theorem exists_prime_factor_boundaryCyclotomicPrimeCore_right_exceptional
    {d x u : ℕ} (hd : Nat.Prime d) (hd5 : 5 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hdx : d ∣ x)
    (hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ boundaryCyclotomicPrimeCore .right d x u ∧ ¬ q ∣ x := by
  simp only [boundaryCyclotomicPrimeCore]
  exact exists_prime_factor_cyclotomicPrimeCore_not_dvd_gap_exceptional
    hd hd5 hx hu hcop hdx hWieferich

end DkMath.CFBRC
