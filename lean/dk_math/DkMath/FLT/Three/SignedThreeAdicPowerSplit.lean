/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.SignedThreeAdic
import Mathlib.Algebra.GCDMonoid.Basic

#print "file: DkMath.FLT.Three.SignedThreeAdicPowerSplit"

namespace DkMath.FLT.Three

/-!
# Exact power split of the signed three-adic packet

The packet already records the ramified gcd.  This module removes that common
factor in `ℕ` and applies the generic coprime-power factor lemma.  It stops
before any quotient by `eisensteinRamifier` is formed.
-/

/-- The exact cube split after the common factor `3` has been assigned. -/
structure SignedThreeAdicPowerSplit (a b c : ℕ) : Type where
  packet : SignedThreeAdicPacket a b c
  A : ℕ
  B : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  coprime_A_B : Nat.Coprime A B
  carrier_eq : packet.carrier = 3 ^ 2 * A ^ 3
  residual_eq : packet.residual = 3 * B ^ 3
  distinguished_eq : packet.distinguished = 3 * A * B
  three_not_dvd_B : ¬ 3 ∣ B

private theorem three_dvd_of_mod_nine_eq_three
    {n : ℕ} (h : n % 9 = 3) : 3 ∣ n := by
  refine ⟨3 * (n / 9) + 1, ?_⟩
  have hs := Nat.mod_add_div n 9
  omega

private theorem cube_factor_split
    {g n x : ℕ} (hcop : Nat.Coprime g n)
    (hbody : g * n = x ^ 3) :
    (∃ A : ℕ, g = A ^ 3) ∧ (∃ B : ℕ, n = B ^ 3) := by
  have hunit : IsUnit (GCDMonoid.gcd g n) := by
    change IsUnit (Nat.gcd g n)
    rw [isUnit_iff_dvd_one]
    simpa [Nat.Coprime] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd n g) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

private theorem nonempty_signedThreeAdicPowerSplit_of_packet
    {a b c : ℕ} (p : SignedThreeAdicPacket a b c) :
    Nonempty {s : SignedThreeAdicPowerSplit a b c // s.packet = p} := by
  let C := p.carrier / 3
  let R := p.residual / 3
  let D := p.distinguished / 3
  have h3res : 3 ∣ p.residual :=
    three_dvd_of_mod_nine_eq_three p.residual_mod_nine
  have hc : p.carrier = 3 * C :=
    (Nat.mul_div_cancel' p.three_dvd_carrier).symm
  have hr : p.residual = 3 * R :=
    (Nat.mul_div_cancel' h3res).symm
  have hd : p.distinguished = 3 * D :=
    (Nat.mul_div_cancel' p.three_dvd_distinguished).symm
  have hcopCR : Nat.Coprime C R := by
    have h := Nat.coprime_div_gcd_div_gcd
      (show 0 < Nat.gcd p.carrier p.residual by
        rw [p.gcd_eq_three]
        decide)
    simpa [C, R, p.gcd_eq_three] using h
  have h3R : ¬ 3 ∣ R := by
    intro h
    have h9 : 9 ∣ p.residual := by
      rcases h with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hr, hk]
      ring
    have hz := Nat.mod_eq_zero_of_dvd h9
    rw [p.residual_mod_nine] at hz
    omega
  have hnormalized : C * R = 3 * D ^ 3 := by
    have hraw : (3 * C) * (3 * R) = (3 * D) ^ 3 := by
      simpa [hc, hr, hd] using p.factorization
    nlinarith
  have h3C : 3 ∣ C := by
    have h3CR : 3 ∣ C * R := by
      rw [hnormalized]
      exact ⟨D ^ 3, by ring⟩
    rcases Nat.prime_three.dvd_mul.mp h3CR with h | h
    · exact h
    · exact (h3R h).elim
  let A := C / 3
  have hC : C = 3 * A :=
    (Nat.mul_div_cancel' h3C).symm
  have hAR : A * R = D ^ 3 := by
    have hcancel : 3 * (A * R) = 3 * D ^ 3 := by
      calc
        3 * (A * R) = C * R := by rw [hC]; ring
        _ = 3 * D ^ 3 := hnormalized
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) hcancel
  have hcopAR : Nat.Coprime A R := by
    apply Nat.Coprime.of_dvd_left (a₁ := A) (a₂ := C)
    · exact ⟨3, by rw [hC]; ring⟩
    · exact hcopCR
  rcases cube_factor_split hcopAR hAR with
    ⟨⟨A0, hA0⟩, ⟨B, hB⟩⟩
  have hcarrier : p.carrier = 3 ^ 2 * A0 ^ 3 := by
    calc
      p.carrier = 3 * C := hc
      _ = 3 * (3 * A) := by rw [hC]
      _ = 3 ^ 2 * A0 ^ 3 := by rw [hA0]; ring
  have hresidual : p.residual = 3 * B ^ 3 := by
    rw [hr, hB]
  have hdistinguished : p.distinguished = 3 * A0 * B := by
    apply Nat.pow_left_injective (by decide : 3 ≠ 0)
    change p.distinguished ^ 3 = (3 * A0 * B) ^ 3
    calc
      p.distinguished ^ 3 = p.carrier * p.residual := p.factorization.symm
      _ = (3 * A0 * B) ^ 3 := by rw [hcarrier, hresidual]; ring
  have hApos : 0 < A0 := by
    by_contra h
    have hzero : A0 = 0 := by omega
    rw [hzero] at hcarrier
    norm_num at hcarrier
    exact (Nat.ne_of_gt p.carrier_pos) hcarrier
  have hBpos : 0 < B := by
    by_contra h
    have hzero : B = 0 := by omega
    rw [hzero] at hresidual
    norm_num at hresidual
    exact (Nat.ne_of_gt p.residual_pos) hresidual
  have hpowcop : Nat.Coprime (A0 ^ 3) (B ^ 3) := by
    simpa [hA0, hB] using hcopAR
  have hcopAB : Nat.Coprime A0 B := by
    apply (Nat.coprime_pow_right_iff (by decide : 0 < 3) A0 B).mp
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 3) A0 (B ^ 3)).mp hpowcop
  have h3B : ¬ 3 ∣ B := by
    intro h
    have h9 : 9 ∣ p.residual := by
      rcases h with ⟨k, hk⟩
      refine ⟨9 * k ^ 3, ?_⟩
      rw [hresidual, hk]
      ring
    have hz := Nat.mod_eq_zero_of_dvd h9
    rw [p.residual_mod_nine] at hz
    omega
  exact ⟨⟨{
    packet := p
    A := A0
    B := B
    A_pos := hApos
    B_pos := hBpos
    coprime_A_B := hcopAB
    carrier_eq := hcarrier
    residual_eq := hresidual
    distinguished_eq := hdistinguished
    three_not_dvd_B := h3B }, rfl⟩⟩

/-- A power split whose packet field is definitionally routed back to `p`. -/
noncomputable def signedThreeAdicPowerSplit_with_packet
    {a b c : ℕ} (p : SignedThreeAdicPacket a b c) :
    {s : SignedThreeAdicPowerSplit a b c // s.packet = p} :=
  Classical.choice (nonempty_signedThreeAdicPowerSplit_of_packet p)

/-- A chosen exact split of a signed three-adic packet. -/
noncomputable def signedThreeAdicPowerSplit_of_packet
    {a b c : ℕ} (p : SignedThreeAdicPacket a b c) :
    SignedThreeAdicPowerSplit a b c :=
  (signedThreeAdicPowerSplit_with_packet p).1

/-- The exact split obtained directly from a positive primitive cubic solution. -/
noncomputable def signedThreeAdicPowerSplit_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    SignedThreeAdicPowerSplit a b c :=
  signedThreeAdicPowerSplit_of_packet
    (signedThreeAdicPacket_of_primitive_solution ha hb hc hab hEq)

/-- The future `lambda * beta` normalization has positive second coordinate `3*A^3`.
This theorem records only its sign contract; it does not construct the quotient `beta`. -/
theorem future_signed_beta_snd_pos
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    0 < 3 * s.A ^ 3 := by
  exact Nat.mul_pos (by decide) (pow_pos s.A_pos 3)

end DkMath.FLT.Three
