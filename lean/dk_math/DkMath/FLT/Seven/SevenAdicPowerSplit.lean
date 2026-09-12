/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CounterexampleRouting
import DkMath.FLT.Prime.AdicPowerSplit

#print "file: DkMath.FLT.Seven.SevenAdicPowerSplit"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

theorem SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
    {x y z : ℕ} (s : SevenAdicCounterexamplePacket x y z) :
    DkMath.FLT.Prime.PrimeAdicFactorPacket 7 (z - y) y x :=
  { prime := by norm_num
    odd := by norm_num
    gap_pos := gap_pos_of_fermat7Equation s.counterexample.hx s.counterexample.hEq
    distinguished_pos := s.counterexample.hx
    coprime_gap_unit := coprime_gap_y_of_counterexamplePack s.counterexample
    prime_dvd_gap := s.seven_dvd_gap
    factor_eq := by simpa using s.factor_eq }

theorem sevenAdicPacket_residual_not_fortyNine_dvd
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 49 ∣ GN 7 (z - y) y := by
  exact p.toPrimeAdicFactorPacket.residual_not_prime_sq

theorem sevenAdicPacket_seven_not_dvd_strippedResidual
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 7 ∣ GN 7 (z - y) y / 7 := by
  have h7res : 7 ∣ GN 7 (z - y) y := by
    exact p.toPrimeAdicFactorPacket.prime_dvd_residual
  intro h7
  apply sevenAdicPacket_residual_not_fortyNine_dvd p
  rw [show 49 = 7 * 7 by norm_num]
  exact Nat.mul_dvd_of_dvd_div h7res h7

theorem sevenAdicPacket_coprime_div_seven
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime ((z - y) / 7) ((GN 7 (z - y) y) / 7) := by
  have h := Nat.coprime_div_gcd_div_gcd
    (show 0 < Nat.gcd (z - y) (GN 7 (z - y) y) by
      rw [p.toPrimeAdicFactorPacket.gcd_gap_residual]
      norm_num)
  rw [p.toPrimeAdicFactorPacket.gcd_gap_residual] at h
  exact h

theorem sevenAdicPacket_coprime_scaledGap_residual
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime (7 ^ 2 * ((z - y) / 7))
      ((GN 7 (z - y) y) / 7) := by
  have h7cop : Nat.Coprime 7 ((GN 7 (z - y) y) / 7) :=
    (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
      (sevenAdicPacket_seven_not_dvd_strippedResidual p)
  exact (h7cop.pow_left 2).mul_left (sevenAdicPacket_coprime_div_seven p)

theorem sevenAdicPacket_normalized_product
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    (7 ^ 2 * ((z - y) / 7)) * ((GN 7 (z - y) y) / 7) =
      (7 * (x / 7)) ^ 7 := by
  have h7res : 7 ∣ GN 7 (z - y) y :=
    p.toPrimeAdicFactorPacket.prime_dvd_residual
  have hgap : z - y = 7 * ((z - y) / 7) :=
    (Nat.mul_div_cancel' p.seven_dvd_gap).symm
  have hres : GN 7 (z - y) y = 7 * (GN 7 (z - y) y / 7) :=
    (Nat.mul_div_cancel' h7res).symm
  have hx : x = 7 * (x / 7) := (Nat.mul_div_cancel' p.seven_dvd_x).symm
  calc
    (7 ^ 2 * ((z - y) / 7)) * (GN 7 (z - y) y / 7) =
        (7 * ((z - y) / 7)) * (7 * (GN 7 (z - y) y / 7)) := by ring
    _ = (z - y) * GN 7 (z - y) y := by rw [← hgap, ← hres]
    _ = x ^ 7 := p.toPrimeAdicFactorPacket.factor_eq
    _ = (7 * (x / 7)) ^ 7 := by rw [← hx]

/-- Exact seventh-power split after assigning the unique common factor seven. -/
structure SevenAdicPowerSplit (x y z : ℕ) : Type where
  sevenAdic : SevenAdicCounterexamplePacket x y z
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  gap_eq : z - y = 7 ^ 6 * a ^ 7
  residual_eq : GN 7 (z - y) y = 7 * b ^ 7
  distinguished_eq : x = 7 * a * b

theorem SevenAdicPowerSplit.seven_not_dvd_b
    {x y z : ℕ} (s : SevenAdicPowerSplit x y z) : ¬ 7 ∣ s.b := by
  intro h7b
  apply s.sevenAdic.toPrimeAdicFactorPacket.residual_not_prime_sq
  rcases h7b with ⟨k, hk⟩
  change 7 ^ 2 ∣ GN 7 (z - y) y
  rw [s.residual_eq, hk]
  use 7 ^ 6 * k ^ 7
  ring

theorem nonempty_sevenAdicPowerSplit_of_packet
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nonempty (SevenAdicPowerSplit x y z) := by
  rcases DkMath.FLT.Prime.nonempty_primeAdicPowerSplit_of_packet
      p.toPrimeAdicFactorPacket with ⟨s⟩
  exact ⟨{
    sevenAdic := p
    a := s.a
    b := s.b
    a_pos := s.a_pos
    b_pos := s.b_pos
    coprime_a_b := s.coprime_a_b
    gap_eq := by simpa using s.gap_eq
    residual_eq := by simpa using s.residual_eq
    distinguished_eq := s.distinguished_eq }⟩

noncomputable def sevenAdicPowerSplit_of_packet
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    SevenAdicPowerSplit x y z :=
  Classical.choice (nonempty_sevenAdicPowerSplit_of_packet p)

noncomputable def sevenAdicPowerSplit_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : SevenAdicPowerSplit x y z :=
  sevenAdicPowerSplit_of_packet
    (sevenAdicCounterexamplePacket_of_branch hPack hBranch)

end DkMath.FLT.Seven
