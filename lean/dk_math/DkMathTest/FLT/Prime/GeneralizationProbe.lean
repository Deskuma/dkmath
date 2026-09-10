/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailBoundary
import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.Lib.NumberTheory.PadicValNat

/-!
# FLT7 prime-exponent generalization probe

This is a focused, non-production probe.  It deliberately does not import or
modify the `DkMath.FLT.Seven` proof tower.  The declarations below test which
parts of its front-half routing are consequences of the reusable `GTail` and
natural valuation layers.
-/

open scoped BigOperators

namespace DkMathTest.FLT.Prime.GeneralizationProbe

open DkMath.CosmicFormula

private lemma sum_range_modEq_zero
    {n m : ℕ} {f : ℕ → ℕ}
    (h : ∀ k, k < m → f k ≡ 0 [MOD n]) :
    (∑ k ∈ Finset.range m, f k) ≡ 0 [MOD n] := by
  induction m with
  | zero => exact Nat.ModEq.rfl
  | succ m ih =>
      rw [Finset.sum_range_succ]
      exact (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))).add
        (h m (Nat.lt_succ_self m))

private lemma sum_range_modEq_last
    {p : ℕ} (hp : 0 < p) {f : ℕ → ℕ} {target : ℕ}
    (hprev : ∀ k, k < p - 1 → f k ≡ 0 [MOD p])
    (hlast : f (p - 1) ≡ target [MOD p]) :
    (∑ k ∈ Finset.range p, f k) ≡ target [MOD p] := by
  have hsplit : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
  have hsum_eq :
      (∑ k ∈ Finset.range p, f k) =
        (∑ k ∈ Finset.range (p - 1), f k) + f (p - 1) := by
    calc
      (∑ k ∈ Finset.range p, f k) =
          ∑ k ∈ Finset.range (p - 1 + 1), f k := by rw [hsplit]
      _ = (∑ k ∈ Finset.range (p - 1), f k) + f (p - 1) := by
        rw [Finset.sum_range_succ]
  rw [hsum_eq]
  simpa using (sum_range_modEq_zero hprev).add hlast

/-! ## Probe A: exact boundary gcd -/

theorem gcd_GN_eq_gcd_of_one_le
    {d g u : ℕ} (hd : 1 ≤ d) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail d 1 g u) = Nat.gcd g d := by
  exact DkMath.CosmicFormula.gcd_GTail_eq_gcd_choose
    d 1 g u hd hcop |>.trans (by simp [Nat.choose_one_right])

theorem gcd_GN_prime_eq_gcd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail p 1 g u) = Nat.gcd g p := by
  exact gcd_GN_eq_gcd_of_one_le hp.one_le hcop

theorem gcd_GN_prime_eq_one_of_not_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : ¬ p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = 1 := by
  rw [gcd_GN_prime_eq_gcd hp hcop]
  have hgcd : Nat.gcd g p ∣ p := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime hp).mp hgcd with h | h
  · exact h
  · exfalso
    apply hpg
    rw [← h]
    exact Nat.gcd_dvd_left _ _

/-! ## Probe B: prime divisibility address -/

private lemma prime_row_modEq_last
    {p g u : ℕ} (hp : Nat.Prime p) :
    GTail p 1 g u ≡ g ^ (p - 1) [MOD p] := by
  let f : ℕ → ℕ := fun k =>
    Nat.choose p (k + 1) * g ^ k * u ^ (p - 1 - k)
  have hsum : GTail p 1 g u = ∑ k ∈ Finset.range p, f k := by
    simpa [f] using (GTail_one_eq_sum (R := ℕ) p g u)
  have hprev : ∀ k, k < p - 1 → f k ≡ 0 [MOD p] := by
    intro k hk
    have hchoose : p ∣ Nat.choose p (k + 1) :=
      hp.dvd_choose_self (by omega) (by omega)
    have hterm : p ∣ f k := by
      dsimp [f]
      simpa [mul_assoc] using
        (dvd_mul_of_dvd_left hchoose (g ^ k * u ^ (p - 1 - k)))
    exact Nat.modEq_zero_iff_dvd.mpr hterm
  have hlast : f (p - 1) ≡ g ^ (p - 1) [MOD p] := by
    dsimp [f]
    have hp1 : 1 ≤ p := hp.one_le
    simpa [Nat.sub_add_cancel hp1] using
      (Nat.ModEq.rfl : g ^ (p - 1) ≡ g ^ (p - 1) [MOD p])
  rw [hsum]
  exact sum_range_modEq_last (Nat.pos_of_ne_zero hp.ne_zero) hprev hlast

theorem prime_dvd_GN_iff_dvd_gap
    {p g u : ℕ} (hp : Nat.Prime p) :
    p ∣ GTail p 1 g u ↔ p ∣ g := by
  constructor
  · intro hGN
    have hzero : GTail p 1 g u ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr hGN
    have hpow : g ^ (p - 1) ≡ 0 [MOD p] :=
      (prime_row_modEq_last hp).symm.trans hzero
    exact hp.dvd_of_dvd_pow (Nat.modEq_zero_iff_dvd.mp hpow)
  · intro hpg
    have hmod := GN_modEq_choose_mul_pow_of_dvd_x
      (d := p) (n := p) g u hp.one_le hpg
    apply Nat.dvd_iff_mod_eq_zero.mpr
    change GTail p 1 g u % p =
      (Nat.choose p 1 * u ^ (p - 1)) % p at hmod
    rw [hmod]
    simp [Nat.choose_one_right]

example (g u : ℕ) :
    2 ∣ GTail 2 1 g u ↔ 2 ∣ g :=
  prime_dvd_GN_iff_dvd_gap (by norm_num)

theorem gcd_GN_prime_eq_prime_of_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = p := by
  rw [gcd_GN_prime_eq_gcd hp hcop]
  apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
  apply Nat.dvd_gcd hpg
  exact Nat.dvd_refl p

/-! ## Probe C: sharpened odd-prime mod-p² congruence -/

theorem GN_modEq_head_mod_sq_of_odd_prime_dvd_x_probe
    {p : ℕ} (g u : ℕ)
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpg : p ∣ g) :
    GTail p 1 g u ≡ p * u ^ (p - 1) [MOD p ^ 2] := by
  simpa [Nat.choose_one_right] using
    (GTail_modEq_head_mod_sq_of_prime_dvd_x
      (p := p) (r := 1) g u hp (by omega) (by omega) hpg)

/-! ## Probe D: exact odd-prime residual valuation -/

theorem padicValNat_GN_prime_eq_one_of_dvd_gap
    {p g u : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    padicValNat p (GTail p 1 g u) = 1 := by
  have hGN : p ∣ GTail p 1 g u :=
    (prime_dvd_GN_iff_dvd_gap hp).2 hpg
  have hpu : ¬ p ∣ u := by
    intro hpu
    have hpgcd : p ∣ Nat.gcd g u := Nat.dvd_gcd hpg hpu
    rw [hcop.gcd_eq_one] at hpgcd
    exact hp.not_dvd_one hpgcd
  have hhead_not : ¬ p ^ 2 ∣ p * u ^ (p - 1) := by
    intro hhead
    rcases hhead with ⟨k, hk⟩
    have hcancel : u ^ (p - 1) = p * k := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
      calc
        p * u ^ (p - 1) = p ^ 2 * k := hk
        _ = p * (p * k) := by ring
    exact hpu (hp.dvd_of_dvd_pow ⟨k, hcancel⟩)
  have hGN_not_sq : ¬ p ^ 2 ∣ GTail p 1 g u := by
    intro hsq
    have hmod := GN_modEq_head_mod_sq_of_odd_prime_dvd_x_probe
      g u hp hp3 hpg
    have hhead_zero : p * u ^ (p - 1) ≡ 0 [MOD p ^ 2] :=
      hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hsq)
    exact hhead_not (Nat.modEq_zero_iff_dvd.mp hhead_zero)
  have hGN0 : GTail p 1 g u ≠ 0 := by
    intro hzero
    apply hGN_not_sq
    rw [hzero]
    exact dvd_zero _
  have hge : 1 ≤ padicValNat p (GTail p 1 g u) :=
    DkMath.Lib.NumberTheory.Vp_ge_one_iff hp hGN0 |>.2 hGN
  have hnotTwo : ¬ 2 ≤ padicValNat p (GTail p 1 g u) := by
    intro htwo
    apply hGN_not_sq
    exact (DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp hGN0 2).mp htwo
  omega

example : GTail 2 1 2 1 = 4 := by
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]

example : padicValNat 2 4 = 2 := by
  have hp : Nat.Prime 2 := by norm_num
  calc
    padicValNat 2 4 = padicValNat 2 (2 ^ 2) := by norm_num
    _ = 2 * padicValNat 2 2 := DkMath.Lib.NumberTheory.padicValNat_pow hp 2 (by norm_num)
    _ = 2 := by norm_num [padicValNat]

/-! ## Probe E: generic power-factor split -/

theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d) := by
  have hunit : IsUnit (GCDMonoid.gcd a b) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd b a) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

/-! ## Probe F: valuation conservation -/

theorem padicValNat_carrier_shape_of_mul_eq_prime
    {p carrier residual distinguished : ℕ}
    (hp : Nat.Prime p)
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ p)
    (hrVal : padicValNat p residual = 1) :
    ∃ m : ℕ,
      padicValNat p carrier = (p - 1) + p * m := by
  have hpow : padicValNat p (distinguished ^ p) =
      p * padicValNat p distinguished :=
    DkMath.Lib.NumberTheory.padicValNat_pow hp p hd0
  have hmul : padicValNat p (carrier * residual) =
      padicValNat p carrier + padicValNat p residual := by
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    simpa using (padicValNat.mul (p := p) hc0 hr0)
  have hvalEq : p * padicValNat p distinguished =
      padicValNat p carrier + 1 := by
    calc
      p * padicValNat p distinguished =
          padicValNat p (distinguished ^ p) := hpow.symm
      _ = padicValNat p (carrier * residual) := by rw [hEq]
      _ = padicValNat p carrier + padicValNat p residual := hmul
      _ = padicValNat p carrier + 1 := by rw [hrVal]
  have hdValPos : 0 < padicValNat p distinguished := by
    have hpos : 0 < p * padicValNat p distinguished := by
      rw [hvalEq]
      omega
    exact Nat.pos_of_mul_pos_left hpos
  have hcVal : padicValNat p carrier =
      p * padicValNat p distinguished - 1 :=
    Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat p distinguished - 1, ?_⟩
  have hsplit :
      (padicValNat p distinguished - 1) + 1 = padicValNat p distinguished :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hdValPos)
  calc
    padicValNat p carrier = p * padicValNat p distinguished - 1 := hcVal
    _ = p * ((padicValNat p distinguished - 1) + 1) - 1 := by rw [hsplit]
    _ = (p - 1) + p * (padicValNat p distinguished - 1) := by
      have hv : 1 ≤ padicValNat p distinguished := Nat.succ_le_of_lt hdValPos
      have hpv : p ≤ p * padicValNat p distinguished := by
        calc
          p = p * 1 := by simp
          _ ≤ p * padicValNat p distinguished := Nat.mul_le_mul_left p hv
      rw [hsplit]
      have hv_eq :
          p * padicValNat p distinguished =
            p * (padicValNat p distinguished - 1) + p := by
        calc
          p * padicValNat p distinguished =
              (p * padicValNat p distinguished - p) + p :=
            (Nat.sub_add_cancel hpv).symm
          _ = p * (padicValNat p distinguished - 1) + p := by
            rw [Nat.mul_sub_left_distrib]
            simp
      rw [hv_eq]
      have hp1 : 1 ≤ p := hp.one_le
      omega

/-! ## Probe G: divisibility consequence -/

theorem prime_pow_sub_one_dvd_carrier
    {p carrier residual distinguished : ℕ}
    (hp : Nat.Prime p)
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ p)
    (hrVal : padicValNat p residual = 1) :
    p ^ (p - 1) ∣ carrier := by
  have hshape := padicValNat_carrier_shape_of_mul_eq_prime
    hp hc0 hr0 hd0 hEq hrVal
  apply (DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp hc0 (p - 1)).mp
  rcases hshape with ⟨m, hm⟩
  rw [hm]
  omega

#print axioms gcd_GN_prime_eq_gcd
#print axioms gcd_GN_prime_eq_one_of_not_dvd
#print axioms gcd_GN_prime_eq_prime_of_dvd
#print axioms prime_dvd_GN_iff_dvd_gap
#print axioms GN_modEq_head_mod_sq_of_odd_prime_dvd_x_probe
#print axioms padicValNat_GN_prime_eq_one_of_dvd_gap
#print axioms power_factor_split
#print axioms padicValNat_carrier_shape_of_mul_eq_prime
#print axioms prime_pow_sub_one_dvd_carrier

end DkMathTest.FLT.Prime.GeneralizationProbe
