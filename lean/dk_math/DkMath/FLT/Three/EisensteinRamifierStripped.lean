/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.SignedThreeAdicPowerSplit

#print "file: DkMath.FLT.Three.EisensteinRamifierStripped"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Eisenstein ramifier stripping

The exact power split supplies `carrier = 9*A^3`.  In the trace-one basis,
this makes the second coordinate of the quotient by `lambda = 1 + tau`
explicitly `3*A^3`; no division operation in the ring is used here.
-/

/-- Multiplication by the ramifier in trace-one coordinates. -/
theorem eisenstein_ramifier_mul_coord (u v : ℤ) :
    eisensteinRamifier * eisensteinCoord u v =
      eisensteinCoord (u - v) (u + 2 * v) := by
  change (⟨1, 1⟩ : TraceOneInt (-1)) * ⟨u, v⟩ =
    (⟨u - v, u + 2 * v⟩ : TraceOneInt (-1))
  ext <;> norm_num [DkMath.NumberTheory.TraceOneQuadratic.mul] <;> ring

/-- The explicit ramifier-free coordinate chosen from a power split. -/
def eisensteinRamifierStrippedBeta
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) : EisensteinInt :=
  eisensteinCoord
    (s.packet.alpha.fst + 3 * (s.A : ℤ) ^ 3)
    (3 * (s.A : ℤ) ^ 3)

/-- The production packet after one exact ramifier removal. -/
structure EisensteinRamifierStrippedPacket
    (a b c : ℕ) : Type where
  powerSplit : SignedThreeAdicPowerSplit a b c
  beta : EisensteinInt
  alpha_eq :
    powerSplit.packet.alpha = eisensteinRamifier * beta
  beta_norm :
    norm beta = (powerSplit.B : ℤ) ^ 3
  beta_snd :
    beta.snd = 3 * (powerSplit.A : ℤ) ^ 3

private theorem signed_gap_eq_nine_cube
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    s.packet.alpha.snd - s.packet.alpha.fst =
      9 * (s.A : ℤ) ^ 3 := by
  rw [s.packet.alpha_signed_gap, s.carrier_eq]
  push_cast
  ring

private theorem alpha_eq_ramifier_mul_stripped_beta
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    s.packet.alpha = eisensteinRamifier * eisensteinRamifierStrippedBeta s := by
  have hgap := signed_gap_eq_nine_cube s
  have hcoords :
      s.packet.alpha = eisensteinCoord s.packet.alpha.fst s.packet.alpha.snd := by
    rfl
  rw [eisensteinRamifierStrippedBeta, eisenstein_ramifier_mul_coord]
  rw [hcoords]
  ext <;> simp only [eisensteinCoord]
  · ring
  · linarith

private theorem stripped_beta_norm
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    norm (eisensteinRamifierStrippedBeta s) = (s.B : ℤ) ^ 3 := by
  have hαβ :
      s.packet.alpha =
        eisensteinRamifier * eisensteinRamifierStrippedBeta s :=
    alpha_eq_ramifier_mul_stripped_beta s
  have hnorm :
      norm s.packet.alpha =
        norm eisensteinRamifier *
          norm (eisensteinRamifierStrippedBeta s) := by
    rw [hαβ, eisenstein_norm_mul]
  rw [s.packet.alpha_norm, eisenstein_ramifier_norm, s.residual_eq] at hnorm
  push_cast at hnorm
  nlinarith

/-- The stripped beta has the mandatory exact second coordinate. -/
theorem eisensteinRamifierStrippedPacket_beta_snd
    {a b c : ℕ} (s : EisensteinRamifierStrippedPacket a b c) :
    s.beta.snd = 3 * (s.powerSplit.A : ℤ) ^ 3 :=
  s.beta_snd

/-- The exact second coordinate is positive, in the integer form used downstream. -/
theorem eisensteinRamifierStrippedPacket_beta_snd_pos
    {a b c : ℕ} (s : EisensteinRamifierStrippedPacket a b c) :
    0 < s.beta.snd := by
  rw [s.beta_snd]
  exact mul_pos (by norm_num)
    (pow_pos (by exact_mod_cast s.powerSplit.A_pos) 3)

/-- The residual base still avoids the ramified prime. -/
theorem eisensteinRamifierStrippedPacket_three_not_dvd_B
    {a b c : ℕ} (s : EisensteinRamifierStrippedPacket a b c) :
    ¬ 3 ∣ s.powerSplit.B :=
  s.powerSplit.three_not_dvd_B

/-- Construct the stripped packet from an exact signed three-adic split. -/
def eisensteinRamifierStrippedPacket_of_powerSplit
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    EisensteinRamifierStrippedPacket a b c := {
  powerSplit := s
  beta := eisensteinRamifierStrippedBeta s
  alpha_eq := alpha_eq_ramifier_mul_stripped_beta s
  beta_norm := stripped_beta_norm s
  beta_snd := rfl }

/-- Construct the stripped packet directly from a positive primitive solution. -/
noncomputable def eisensteinRamifierStrippedPacket_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    EisensteinRamifierStrippedPacket a b c :=
  eisensteinRamifierStrippedPacket_of_powerSplit
    (signedThreeAdicPowerSplit_of_primitive_solution ha hb hc hab hEq)

end DkMath.FLT.Three
