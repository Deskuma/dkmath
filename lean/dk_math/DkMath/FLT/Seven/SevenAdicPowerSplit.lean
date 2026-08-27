/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CounterexampleRouting

#print "file: DkMath.FLT.Seven.SevenAdicPowerSplit"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

theorem sevenAdicPacket_residual_not_fortyNine_dvd
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 49 ∣ GN 7 (z - y) y := by
  exact not_fortyNine_dvd_GN_seven_sub
    (right_lt_of_fermat7Equation p.counterexample.hx p.counterexample.hEq).le
    (coprime_y_z_of_counterexamplePack p.counterexample).symm p.seven_dvd_gap

theorem sevenAdicPacket_seven_not_dvd_strippedResidual
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 7 ∣ GN 7 (z - y) y / 7 := by
  have h7res : 7 ∣ GN 7 (z - y) y := by
    have h := Nat.gcd_dvd_right (z - y) (GN 7 (z - y) y)
    rw [p.gcd_eq_seven] at h
    exact h
  intro h7
  apply sevenAdicPacket_residual_not_fortyNine_dvd p
  rw [show 49 = 7 * 7 by norm_num]
  exact Nat.mul_dvd_of_dvd_div h7res h7

theorem sevenAdicPacket_coprime_div_seven
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime ((z - y) / 7) ((GN 7 (z - y) y) / 7) := by
  have h := Nat.coprime_div_gcd_div_gcd
    (show 0 < Nat.gcd (z - y) (GN 7 (z - y) y) by
      rw [p.gcd_eq_seven]
      norm_num)
  rw [p.gcd_eq_seven] at h
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
  have h7res : 7 ∣ GN 7 (z - y) y := by
    have h := Nat.gcd_dvd_right (z - y) (GN 7 (z - y) y)
    rw [p.gcd_eq_seven] at h
    exact h
  have hgap : z - y = 7 * ((z - y) / 7) :=
    (Nat.mul_div_cancel' p.seven_dvd_gap).symm
  have hres : GN 7 (z - y) y = 7 * (GN 7 (z - y) y / 7) :=
    (Nat.mul_div_cancel' h7res).symm
  have hx : x = 7 * (x / 7) := (Nat.mul_div_cancel' p.seven_dvd_x).symm
  calc
    (7 ^ 2 * ((z - y) / 7)) * (GN 7 (z - y) y / 7) =
        (7 * ((z - y) / 7)) * (7 * (GN 7 (z - y) y / 7)) := by ring
    _ = (z - y) * GN 7 (z - y) y := by rw [← hgap, ← hres]
    _ = x ^ 7 := p.factor_eq
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
  apply sevenAdicPacket_residual_not_fortyNine_dvd s.sevenAdic
  rcases h7b with ⟨k, hk⟩
  rw [s.residual_eq, hk]
  use 7 ^ 6 * k ^ 7
  ring

theorem nonempty_sevenAdicPowerSplit_of_packet
    {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nonempty (SevenAdicPowerSplit x y z) := by
  let c := (z - y) / 7
  let r := GN 7 (z - y) y / 7
  let d := x / 7
  have h7res : 7 ∣ GN 7 (z - y) y := by
    have h := Nat.gcd_dvd_right (z - y) (GN 7 (z - y) y)
    rw [p.gcd_eq_seven] at h
    exact h
  have hc : z - y = 7 * c := (Nat.mul_div_cancel' p.seven_dvd_gap).symm
  have hr : GN 7 (z - y) y = 7 * r := (Nat.mul_div_cancel' h7res).symm
  have hd : x = 7 * d := (Nat.mul_div_cancel' p.seven_dvd_x).symm
  have hcop : Nat.Coprime (7 ^ 2 * c) r :=
    sevenAdicPacket_coprime_scaledGap_residual p
  have hnormalized : (7 ^ 2 * c) * r = (7 * d) ^ 7 :=
    sevenAdicPacket_normalized_product p
  rcases seventh_power_factor_split hcop hnormalized with
    ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
  have h7A : 7 ∣ A := by
    apply (by norm_num : Nat.Prime 7).dvd_of_dvd_pow
    rw [← hA]
    exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 7 ^ 2) c
  rcases h7A with ⟨a, haA⟩
  have hcExact : c = 7 ^ 5 * a ^ 7 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7 ^ 2)
    calc
      7 ^ 2 * c = A ^ 7 := hA
      _ = (7 * a) ^ 7 := by rw [haA]
      _ = 7 ^ 2 * (7 ^ 5 * a ^ 7) := by ring
  have hgap : z - y = 7 ^ 6 * a ^ 7 := by rw [hc, hcExact]; ring
  have hres : GN 7 (z - y) y = 7 * b ^ 7 := by rw [hr, hb]
  have hdist : x = 7 * a * b := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    change x ^ 7 = (7 * a * b) ^ 7
    calc
      x ^ 7 = (z - y) * GN 7 (z - y) y := p.factor_eq.symm
      _ = (7 ^ 6 * a ^ 7) * (7 * b ^ 7) := congrArg₂ (· * ·) hgap hres
      _ = (7 * a * b) ^ 7 := by ring
  have haPos : 0 < a := by
    by_contra ha0
    have : a = 0 := by omega
    rw [this] at hgap
    norm_num at hgap
    exact (gap_pos_of_fermat7Equation p.counterexample.hx p.counterexample.hEq).ne' hgap
  have hbPos : 0 < b := by
    by_contra hb0
    have : b = 0 := by omega
    have hres0 : GN 7 (z - y) y = 0 := by rw [hres, this]; norm_num
    exact (GN_seven_pos_of_counterexample p.counterexample).ne' hres0
  have hcoreCoprime : Nat.Coprime (7 ^ 5 * a ^ 7) (b ^ 7) := by
    have h := sevenAdicPacket_coprime_div_seven p
    change Nat.Coprime c r at h
    rw [hcExact, hb] at h
    exact h
  have hpows : Nat.Coprime (a ^ 7) (b ^ 7) :=
    hcoreCoprime.of_dvd_left (dvd_mul_left (a ^ 7) (7 ^ 5))
  have hab : Nat.Coprime a b := by
    apply (Nat.coprime_pow_right_iff (by decide : 0 < 7) a b).mp
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 7) a (b ^ 7)).mp hpows
  exact ⟨{
    sevenAdic := p
    a := a
    b := b
    a_pos := haPos
    b_pos := hbPos
    coprime_a_b := hab
    gap_eq := hgap
    residual_eq := hres
    distinguished_eq := hdist }⟩

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
