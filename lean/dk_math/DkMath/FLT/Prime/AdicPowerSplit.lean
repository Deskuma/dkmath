/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailPadic
import DkMath.Lib.NumberTheory.PowerFactor

#print "file: DkMath.FLT.Prime.AdicPowerSplit"

/-!
# Generic odd-prime adic power split

This module packages the arithmetic front half isolated from the FLT7
`TraceOneInt`, axis-depth, real-cubic, and degree-six layers.  It is not a
general FLT theorem.
-/

namespace DkMath.FLT.Prime

open DkMath.CosmicFormula

/-- The generic odd-prime arithmetic input for a normalized `GTail` residual. -/
structure PrimeAdicFactorPacket (p g u x : ℕ) : Prop where
  prime : Nat.Prime p
  odd : 3 ≤ p
  gap_pos : 0 < g
  distinguished_pos : 0 < x
  coprime_gap_unit : Nat.Coprime g u
  prime_dvd_gap : p ∣ g
  factor_eq : g * GTail p 1 g u = x ^ p

theorem PrimeAdicFactorPacket.prime_dvd_residual
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    p ∣ GTail p 1 g u :=
  (prime_dvd_GN_iff_dvd_gap P.prime).2 P.prime_dvd_gap

theorem PrimeAdicFactorPacket.gcd_gap_residual
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    Nat.gcd g (GTail p 1 g u) = p :=
  gcd_GN_prime_eq_prime_of_dvd P.prime P.coprime_gap_unit P.prime_dvd_gap

theorem PrimeAdicFactorPacket.residual_exact_one
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    padicValNat p (GTail p 1 g u) = 1 :=
  padicValNat_GN_prime_eq_one_of_dvd_gap
    P.prime P.odd P.coprime_gap_unit P.prime_dvd_gap

theorem PrimeAdicFactorPacket.residual_not_prime_sq
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    ¬ p ^ 2 ∣ GTail p 1 g u :=
  not_prime_sq_dvd_GN_of_dvd_gap
    P.prime P.odd P.coprime_gap_unit P.prime_dvd_gap

theorem PrimeAdicFactorPacket.prime_dvd_distinguished
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    p ∣ x := by
  apply P.prime.dvd_of_dvd_pow
  rw [← P.factor_eq]
  exact dvd_mul_of_dvd_left P.prime_dvd_gap _

theorem PrimeAdicFactorPacket.residual_pos
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    0 < GTail p 1 g u := by
  have hxpow : 0 < x ^ p := pow_pos P.distinguished_pos p
  nlinarith [P.factor_eq]

/-! ## The output normal form -/

structure PrimeAdicPowerSplit (p g u x : ℕ) : Type where
  input : PrimeAdicFactorPacket p g u x
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  gap_eq : g = p ^ (p - 1) * a ^ p
  residual_eq : GTail p 1 g u = p * b ^ p
  distinguished_eq : x = p * a * b
  prime_not_dvd_b : ¬ p ∣ b

private theorem PrimeAdicFactorPacket.stripped_coprime
    {p g u x c r : ℕ} (P : PrimeAdicFactorPacket p g u x)
    (hc : g = p * c) (hr : GTail p 1 g u = p * r) :
    Nat.Coprime c r := by
  have hgcd : Nat.gcd g (GTail p 1 g u) = p := P.gcd_gap_residual
  have h := Nat.coprime_div_gcd_div_gcd
    (show 0 < Nat.gcd g (GTail p 1 g u) by rw [hgcd]; exact P.prime.pos)
  rw [hgcd] at h
  have hgc : g / p = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c P.prime.pos
  have hgr : GTail p 1 g u / p = r := by
    rw [hr]
    exact Nat.mul_div_cancel_left r P.prime.pos
  rw [hgc, hgr] at h
  exact h

private theorem PrimeAdicFactorPacket.stripped_residual_not_dvd
    {p g u x r : ℕ} (P : PrimeAdicFactorPacket p g u x)
    (hr : GTail p 1 g u = p * r) :
    ¬ p ∣ r := by
  intro hpr
  apply P.residual_not_prime_sq
  rcases hpr with ⟨k, hk⟩
  rw [hr, hk]
  use k
  ring

private theorem prime_pow_factor_exponent
    {p a c : ℕ} (_hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hEq : p ^ 2 * c = (p * a) ^ p) :
    c = p ^ (p - 2) * a ^ p := by
  have hp2 : 2 ≤ p := by omega
  have hpexp : p - 2 + 2 = p := Nat.sub_add_cancel hp2
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p ^ 2)
  calc
    p ^ 2 * c = (p * a) ^ p := hEq
    _ = p ^ p * a ^ p := by rw [Nat.mul_pow]
    _ = p ^ (p - 2 + 2) * a ^ p := by rw [hpexp]
    _ = (p ^ (p - 2) * p ^ 2) * a ^ p := by rw [pow_add]
    _ = p ^ 2 * (p ^ (p - 2) * a ^ p) := by ring

private theorem prime_gap_factor_exponent
    {p a c g : ℕ} (_hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hc : g = p * c)
    (hEq : p ^ 2 * c = (p * a) ^ p) :
    g = p ^ (p - 1) * a ^ p := by
  have hcExact := prime_pow_factor_exponent _hp hp3 hEq
  have hpexp : p - 2 + 1 = p - 1 := by omega
  calc
    g = p * c := hc
    _ = p * (p ^ (p - 2) * a ^ p) := by rw [hcExact]
    _ = p ^ (p - 1) * a ^ p := by
      rw [← hpexp, pow_succ]
      ring

private theorem prime_power_factor_split_of_packet
    {p g u x c r d : ℕ} (P : PrimeAdicFactorPacket p g u x)
    (hc : g = p * c)
    (hr : GTail p 1 g u = p * r)
    (hcopcr : Nat.Coprime c r)
    (hnormalized : (p ^ 2 * c) * r = (p * d) ^ p) :
    ∃ a b : ℕ,
      p ^ 2 * c = (p * a) ^ p ∧
      r = b ^ p ∧
      0 < a ∧ 0 < b ∧
      Nat.Coprime a b ∧
      g = p ^ (p - 1) * a ^ p ∧
      GTail p 1 g u = p * b ^ p ∧
      x = p * a * b ∧
      ¬ p ∣ b := by
  have hp2cop : Nat.Coprime (p ^ 2) r :=
    P.prime.coprime_iff_not_dvd.mpr (P.stripped_residual_not_dvd hr) |>.pow_left 2
  have hcop : Nat.Coprime (p ^ 2 * c) r := hp2cop.mul_left hcopcr
  rcases DkMath.Lib.NumberTheory.power_factor_split hcop hnormalized with
    ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
  have hpA : p ∣ A := by
    apply P.prime.dvd_of_dvd_pow
    rw [← hA]
    exact dvd_mul_of_dvd_left (show p ∣ p ^ 2 by
      use p
      ring) c
  rcases hpA with ⟨a, haA⟩
  have hEqA : p ^ 2 * c = (p * a) ^ p := by
    calc
      p ^ 2 * c = A ^ p := hA
      _ = (p * a) ^ p := by rw [haA]
  have hcExact : c = p ^ (p - 2) * a ^ p := by
    exact prime_pow_factor_exponent P.prime P.odd hEqA
  have hgap : g = p ^ (p - 1) * a ^ p :=
    prime_gap_factor_exponent P.prime P.odd hc hEqA
  have hres : GTail p 1 g u = p * b ^ p := by rw [hr, hb]
  have hpPow : p ^ (p - 1) * p = p ^ p := by
    have hp1 : 1 ≤ p := P.prime.one_le
    rw [← pow_succ]
    congr 1
    omega
  have hdist : x = p * a * b := by
    apply Nat.pow_left_injective P.prime.ne_zero
    change x ^ p = (p * a * b) ^ p
    calc
      x ^ p = g * GTail p 1 g u := P.factor_eq.symm
      _ = (p ^ (p - 1) * a ^ p) * (p * b ^ p) :=
        congrArg₂ (· * ·) hgap hres
      _ = (p ^ (p - 1) * p) * a ^ p * b ^ p := by ring
      _ = p ^ p * a ^ p * b ^ p := by rw [hpPow]
      _ = (p * a * b) ^ p := by
        rw [Nat.mul_pow, Nat.mul_pow]
  have hapos : 0 < a := by
    by_contra ha0
    have ha0' : a = 0 := by omega
    have hg0 : g = 0 := by
      simpa [ha0', zero_pow (Nat.ne_of_gt P.prime.pos)] using hgap
    exact P.gap_pos.ne' hg0
  have hbpos : 0 < b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    have hr0 : GTail p 1 g u = 0 := by
      simpa [hb0', zero_pow (Nat.ne_of_gt P.prime.pos)] using hres
    exact P.residual_pos.ne' hr0
  have hcoreCoprime : Nat.Coprime (p ^ (p - 2) * a ^ p) (b ^ p) := by
    rw [hcExact, hb] at hcopcr
    exact hcopcr
  have hpows : Nat.Coprime (a ^ p) (b ^ p) :=
    hcoreCoprime.of_dvd_left (dvd_mul_left (a ^ p) (p ^ (p - 2)))
  have hab : Nat.Coprime a b := by
    apply (Nat.coprime_pow_right_iff P.prime.pos a b).mp
    exact (Nat.coprime_pow_left_iff P.prime.pos a (b ^ p)).mp hpows
  have hnotb : ¬ p ∣ b := by
    intro hpb
    apply P.stripped_residual_not_dvd hr
    have hpbpow : p ∣ b ^ p :=
      hpb.trans (dvd_pow_self b (Nat.ne_of_gt P.prime.pos))
    rw [hb]
    exact hpbpow
  exact ⟨a, b, hEqA, hb, hapos, hbpos, hab,
    hgap, hres, hdist, hnotb⟩

theorem nonempty_primeAdicPowerSplit_of_packet
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    Nonempty (PrimeAdicPowerSplit p g u x) := by
  let c := g / p
  let r := GTail p 1 g u / p
  let d := x / p
  have hpx : p ∣ x := P.prime_dvd_distinguished
  have hc : g = p * c := (Nat.mul_div_cancel' P.prime_dvd_gap).symm
  have hr : GTail p 1 g u = p * r :=
    (Nat.mul_div_cancel' P.prime_dvd_residual).symm
  have hd : x = p * d := (Nat.mul_div_cancel' hpx).symm
  have hcopcr : Nat.Coprime c r := P.stripped_coprime hc hr
  have hnormalized : (p ^ 2 * c) * r = (p * d) ^ p := by
    calc
      (p ^ 2 * c) * r = (p * c) * (p * r) := by ring
      _ = g * GTail p 1 g u := by rw [← hc, ← hr]
      _ = x ^ p := P.factor_eq
      _ = (p * d) ^ p := by rw [hd]
  rcases prime_power_factor_split_of_packet P hc hr hcopcr hnormalized with
    ⟨a, b, hA, hb, haPos, hbPos, hab, hgap, hres, hdist, hnotb⟩
  exact ⟨{
    input := P
    a := a
    b := b
    a_pos := haPos
    b_pos := hbPos
    coprime_a_b := hab
    gap_eq := hgap
    residual_eq := hres
    distinguished_eq := hdist
    prime_not_dvd_b := hnotb }⟩

noncomputable def primeAdicPowerSplit_of_packet
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    PrimeAdicPowerSplit p g u x :=
  Classical.choice (nonempty_primeAdicPowerSplit_of_packet P)

end DkMath.FLT.Prime
