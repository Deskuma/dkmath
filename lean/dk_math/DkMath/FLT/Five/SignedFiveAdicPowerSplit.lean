/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedFiveAdic
import DkMath.FLT.Five.Reduction

#print "file: DkMath.FLT.Five.SignedFiveAdicPowerSplit"

namespace DkMath.FLT.Five

/-!
# Removing the exact five-adic load

The carrier and residual have gcd exactly five.  Removing it and splitting the remaining
coprime fifth-power product yields

`carrier = 5^4*a^5`, `residual = 5*b^5`, `distinguished = 5*a*b`,

with positive coprime `a,b` and `5` absent from `b`.  These retained coprimality facts
are the input for stripping the ramified element in the quadratic order.
-/

private theorem dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
    {u v q : ℕ} (hqsum : q ∣ u + v) (hqres : q ∣ SumGN5 u v) :
    q ∣ 5 * u ^ 4 := by
  have hsumZ : (u : ZMod q) + (v : ZMod q) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff (u + v) q).2 hqsum
  have hvZ : (v : ZMod q) = -(u : ZMod q) :=
    eq_neg_of_add_eq_zero_right hsumZ
  have hresZ : (SumGN5 u v : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (SumGN5 u v) q).2 hqres
  apply (ZMod.natCast_eq_zero_iff (5 * u ^ 4) q).1
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub h] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ
  · have huv : u ≤ v := Nat.le_of_not_ge h
    rw [SumGN5, if_neg h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub huv] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ

/-- The carrier and residual share exactly one factor of five in either source. -/
theorem signedFiveAdicPacket_gcd_eq_five
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nat.gcd p.carrier p.residual = 5 := by
  apply Nat.dvd_antisymm
  · cases p.source with
    | difference hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hgapV : Nat.Coprime (w - v) v :=
          coprime_gap_y_of_counterexamplePack p.normal.pack
        have hDcopV : Nat.Coprime (Nat.gcd (w - v) (GN5 (w - v) v)) v :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hgapV
        have hDcopV4 := Nat.Coprime.pow_right 4 hDcopV
        apply hDcopV4.dvd_of_dvd_mul_right
        exact dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    | sum hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hsumU : Nat.Coprime (u + v) u :=
          Nat.coprime_self_add_left.mpr p.normal.pack.hxy.symm
        have hDcopU : Nat.Coprime (Nat.gcd (u + v) (SumGN5 u v)) u :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hsumU
        have hDcopU4 := Nat.Coprime.pow_right 4 hDcopU
        apply hDcopU4.dvd_of_dvd_mul_right
        exact dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  · have h5res : 5 ∣ p.residual := by
      rcases p.residual_shape with ⟨M, hM⟩
      use 1 + 5 * M
      omega
    exact Nat.dvd_gcd p.five_dvd_carrier h5res

/-- Exact fifth-power split after assigning the unique common factor five. -/
structure SignedFiveAdicPowerSplit
    (u v w : ℕ) : Type where
  fiveAdic : SignedFiveAdicPacket u v w
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  carrier_eq : fiveAdic.carrier = 5 ^ 4 * a ^ 5
  residual_eq : fiveAdic.residual = 5 * b ^ 5
  distinguished_eq : fiveAdic.distinguished = 5 * a * b

/-- The residual fifth-power base retains no factor of five. -/
theorem SignedFiveAdicPowerSplit.five_not_dvd_b
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) : ¬ 5 ∣ s.b := by
  intro h5b
  have h25 : 25 ∣ s.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [s.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [s.fiveAdic.residual_mod_twentyFive] at hzero
  omega

/-- Coprimality needed after the ramifier is stripped. -/
theorem SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (5 ^ 15 * s.a ^ 20) (s.b ^ 5) := by
  have h5b : Nat.Coprime 5 s.b :=
    (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr s.five_not_dvd_b
  have hscaled : Nat.Coprime (5 ^ 15) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 15 h5b).pow_right 5
  have hab : Nat.Coprime (s.a ^ 20) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 20 s.coprime_a_b).pow_right 5
  exact hscaled.mul_left hab

theorem SignedFiveAdicPowerSplit.coprime_b5_scaled_a20
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (s.b ^ 5) (5 ^ 15 * s.a ^ 20) :=
  s.coprime_scaled_a20_b5.symm

private theorem nonempty_signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nonempty (SignedFiveAdicPowerSplit u v w) := by
  let c := p.carrier / 5
  let r := p.residual / 5
  let d := p.distinguished / 5
  have h5res : 5 ∣ p.residual := by
    rcases p.residual_shape with ⟨M, hM⟩
    use 1 + 5 * M
    omega
  have hc : p.carrier = 5 * c := (Nat.mul_div_cancel' p.five_dvd_carrier).symm
  have hr : p.residual = 5 * r := (Nat.mul_div_cancel' h5res).symm
  have hd : p.distinguished = 5 * d :=
    (Nat.mul_div_cancel' p.five_dvd_distinguished).symm
  have hgcd : Nat.gcd p.carrier p.residual = 5 :=
    signedFiveAdicPacket_gcd_eq_five p
  have hcopcr : Nat.Coprime c r := by
    have h := Nat.coprime_div_gcd_div_gcd
      (show 0 < Nat.gcd p.carrier p.residual by rw [hgcd]; decide)
    simpa [c, r, hgcd] using h
  have h5r : ¬ 5 ∣ r := by
    intro h
    have h25 : 25 ∣ p.residual := by
      rcases h with ⟨k, hk⟩
      use k
      rw [hr, hk]
      ring
    have hzero := Nat.mod_eq_zero_of_dvd h25
    rw [p.residual_mod_twentyFive] at hzero
    omega
  have h5copr : Nat.Coprime 5 r :=
    (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5r
  have h25copr : Nat.Coprime 25 r := h5copr.mul_left h5copr
  have hnormalized : (25 * c) * r = (5 * d) ^ 5 := by
    calc
      (25 * c) * r = p.carrier * p.residual := by rw [hc, hr]; ring
      _ = p.distinguished ^ 5 := p.factor_eq
      _ = (5 * d) ^ 5 := by rw [hd]
  have hcop25c : Nat.Coprime (25 * c) r := h25copr.mul_left hcopcr
  rcases fifth_power_factor_split hcop25c hnormalized with
    ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
  have h5A : 5 ∣ A := by
    apply (show Nat.Prime 5 by decide).dvd_of_dvd_pow
    rw [← hA]
    use 5 * c
    ring
  rcases h5A with ⟨a, haA⟩
  have hcExact : c = 5 ^ 3 * a ^ 5 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 25)
    calc
      25 * c = A ^ 5 := hA
      _ = (5 * a) ^ 5 := by rw [haA]
      _ = 25 * (5 ^ 3 * a ^ 5) := by ring
  have hcarrier : p.carrier = 5 ^ 4 * a ^ 5 := by
    rw [hc, hcExact]
    ring
  have hresidual : p.residual = 5 * b ^ 5 := by rw [hr, hb]
  have hdistinguished : p.distinguished = 5 * a * b := by
    apply Nat.pow_left_injective (by decide : 5 ≠ 0)
    change p.distinguished ^ 5 = (5 * a * b) ^ 5
    calc
      p.distinguished ^ 5 = p.carrier * p.residual := p.factor_eq.symm
      _ = (5 * a * b) ^ 5 := by rw [hcarrier, hresidual]; ring
  have haPos : 0 < a := by
    by_contra ha0
    have : a = 0 := by omega
    rw [this] at hcarrier
    norm_num at hcarrier
    exact (Nat.ne_of_gt p.carrier_pos) hcarrier
  have hbPos : 0 < b := by
    by_contra hb0
    have : b = 0 := by omega
    rw [this] at hresidual
    norm_num at hresidual
    exact (Nat.ne_of_gt p.residual_pos) hresidual
  have hcoreCoprime : Nat.Coprime (5 ^ 3 * a ^ 5) (b ^ 5) := by
    simpa [hcExact, hb] using hcopcr
  have hpows : Nat.Coprime (a ^ 5) (b ^ 5) :=
    hcoreCoprime.of_dvd_left (dvd_mul_left (a ^ 5) (5 ^ 3))
  have hab : Nat.Coprime a b := by
    apply (Nat.coprime_pow_right_iff (by decide : 0 < 5) a b).mp
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 5) a (b ^ 5)).mp hpows
  exact ⟨{
    fiveAdic := p
    a := a
    b := b
    a_pos := haPos
    b_pos := hbPos
    coprime_a_b := hab
    carrier_eq := hcarrier
    residual_eq := hresidual
    distinguished_eq := hdistinguished }⟩

/-- Chosen exact power split of a signed five-adic packet. -/
noncomputable def signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    SignedFiveAdicPowerSplit u v w :=
  Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)

/-- Chosen exact power split obtained directly from a signed normal form. -/
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)

/-- Receiver contract for contradictions stated on the exact power-split packet. -/
abbrev SignedFiveAdicPowerSplitCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False

/-- A refuter for every exact power split refutes both signed orientations. -/
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)

/-- The exact power-split core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch

end DkMath.FLT.Five
