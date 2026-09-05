/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinUnitSectors

#print "file: DkMath.FLT.Three.EisensteinSectorExclusion"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Eisenstein sector exclusion

The exact second coordinate of the stripped beta and the condition `3 ∤ B`
force a cube-up-to-unit packet into the one sector.  This module stops after
the resulting exact cube and its two coordinate identities.
-/

/-- The second coordinate of `tau * gamma^3` in the trace-one convention. -/
theorem eisenstein_tau_mul_cube_snd (r s : ℤ) :
    (eisensteinTau * (eisensteinCoord r s) ^ 3).snd =
      r ^ 3 + 3 * r ^ 2 * s - s ^ 3 := by
  rw [eisenstein_cube_coords]
  simp [eisensteinTau, eisensteinCoord, tau]
  ring

/-- The second coordinate of `tau^2 * gamma^3` in the trace-one convention. -/
theorem eisenstein_tau_sq_mul_cube_snd (r s : ℤ) :
    (eisensteinTau ^ 2 * (eisensteinCoord r s) ^ 3).snd =
      r ^ 3 - 3 * r * s ^ 2 - s ^ 3 := by
  rw [eisenstein_tau_sq, eisenstein_cube_coords]
  simp [eisensteinTau, eisensteinCoord, tau]

/-- A cube difference divisible by three has a difference divisible by three. -/
private theorem three_dvd_sub_of_three_dvd_cube_sub
    {r s : ℤ} (h : (3 : ℤ) ∣ r ^ 3 - s ^ 3) :
    (3 : ℤ) ∣ r - s := by
  have hzero : ((r ^ 3 - s ^ 3 : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (r ^ 3 - s ^ 3) 3).mpr h
  have hdiff : (((r - s : ℤ) : ZMod 3) ^ 3) = 0 := by
    calc
      (((r - s : ℤ) : ZMod 3) ^ 3) =
          ((r ^ 3 - s ^ 3 : ℤ) : ZMod 3) := by
            push_cast
            ring_nf
            have h3 : (3 : ZMod 3) = 0 := by exact ZMod.natCast_self 3
            simp only [h3, mul_zero, sub_zero, zero_add]
      _ = 0 := hzero
  have hcast : ((r - s : ℤ) : ZMod 3) = 0 :=
    eq_zero_of_pow_eq_zero hdiff
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (r - s) 3).mp hcast

/-- If `r-s` is divisible by three, then the Eisenstein norm is too. -/
theorem three_dvd_eisenstein_norm_of_three_dvd_sub
    {r s : ℤ} (h : (3 : ℤ) ∣ r - s) :
    (3 : ℤ) ∣ norm (eisensteinCoord r s) := by
  rw [eisenstein_norm_coords]
  rcases h with ⟨k, hk⟩
  have hrs : r = s + 3 * k := by omega
  rw [hrs]
  refine ⟨s ^ 2 + 3 * s * k + 3 * k ^ 2, ?_⟩
  ring

/-- The norm of the adjusted cube root is exactly the residual base `B`. -/
theorem EisensteinCubeSectorPacket.gamma_norm_eq_B
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    norm p.gamma =
      (p.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.B : ℤ) := by
  let q := p.cubeUpToUnit.conjugateCoprime.stripped
  have hcube : norm p.gamma ^ 3 = (q.powerSplit.B : ℤ) ^ 3 := by
    calc
      norm p.gamma ^ 3 = norm (p.sector.rep * p.gamma ^ 3) := by
        rw [eisenstein_norm_mul, p.sector.rep_norm]
        have hnormpow : norm (p.gamma ^ 3) = norm p.gamma ^ 3 := by
          calc
            norm (p.gamma ^ 3) = norm (p.gamma ^ 2 * p.gamma) := by
              congr 1
            _ = norm (p.gamma ^ 2) * norm p.gamma :=
              traceOne_norm_mul _ _
            _ = (norm p.gamma * norm p.gamma) * norm p.gamma := by
              rw [show p.gamma ^ 2 = p.gamma * p.gamma by ring,
                traceOne_norm_mul]
            _ = norm p.gamma ^ 3 := by ring
        rw [hnormpow]
        ring
      _ = norm q.beta := by
        rw [← p.beta_eq]
      _ = (q.powerSplit.B : ℤ) ^ 3 := q.beta_norm
  exact (show Odd 3 by decide).pow_injective hcube

/-- The tau sector is incompatible with `3 ∤ B`. -/
theorem tau_sector_false
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c)
    (hsector : p.sector = .tau) :
    False := by
  let q := p.cubeUpToUnit.conjugateCoprime.stripped
  have hsecond :
      (p.sector.rep * p.gamma ^ 3).snd =
        3 * (q.powerSplit.A : ℤ) ^ 3 := by
    rw [← p.beta_eq]
    exact q.beta_snd
  have hgamma : p.gamma = eisensteinCoord p.gamma.fst p.gamma.snd := by
    rfl
  have hformula :
      p.gamma.fst ^ 3 + 3 * p.gamma.fst ^ 2 * p.gamma.snd -
          p.gamma.snd ^ 3 =
        3 * (q.powerSplit.A : ℤ) ^ 3 := by
    have hsecond' := hsecond
    rw [hsector, EisensteinUnitSector.rep, hgamma] at hsecond'
    simpa only [eisenstein_tau_mul_cube_snd] using hsecond'
  have hdivformula :
      (3 : ℤ) ∣ p.gamma.fst ^ 3 + 3 * p.gamma.fst ^ 2 * p.gamma.snd -
          p.gamma.snd ^ 3 := by
    exact ⟨(q.powerSplit.A : ℤ) ^ 3, hformula⟩
  have hdivcube :
      (3 : ℤ) ∣ p.gamma.fst ^ 3 - p.gamma.snd ^ 3 := by
    refine ⟨(q.powerSplit.A : ℤ) ^ 3 -
      p.gamma.fst ^ 2 * p.gamma.snd, ?_⟩
    calc
      p.gamma.fst ^ 3 - p.gamma.snd ^ 3 =
          (p.gamma.fst ^ 3 + 3 * p.gamma.fst ^ 2 * p.gamma.snd -
            p.gamma.snd ^ 3) - 3 * p.gamma.fst ^ 2 * p.gamma.snd := by ring
      _ = 3 * (q.powerSplit.A : ℤ) ^ 3 -
          3 * p.gamma.fst ^ 2 * p.gamma.snd := by rw [hformula]
      _ = 3 * ((q.powerSplit.A : ℤ) ^ 3 -
          p.gamma.fst ^ 2 * p.gamma.snd) := by ring
  have hsub : (3 : ℤ) ∣ p.gamma.fst - p.gamma.snd :=
    three_dvd_sub_of_three_dvd_cube_sub hdivcube
  have hnormdiv : (3 : ℤ) ∣ norm p.gamma := by
    rw [show p.gamma = eisensteinCoord p.gamma.fst p.gamma.snd by rfl]
    exact three_dvd_eisenstein_norm_of_three_dvd_sub hsub
  have hBdiv : (3 : ℤ) ∣ (q.powerSplit.B : ℤ) := by
    simpa [EisensteinCubeSectorPacket.gamma_norm_eq_B p] using hnormdiv
  have hBNat : 3 ∣ q.powerSplit.B := by
    exact_mod_cast hBdiv
  exact q.powerSplit.three_not_dvd_B hBNat

/-- The `tau^2` sector is incompatible with `3 ∤ B`. -/
theorem tauSq_sector_false
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c)
    (hsector : p.sector = .tauSq) :
    False := by
  let q := p.cubeUpToUnit.conjugateCoprime.stripped
  have hsecond :
      (p.sector.rep * p.gamma ^ 3).snd =
        3 * (q.powerSplit.A : ℤ) ^ 3 := by
    rw [← p.beta_eq]
    exact q.beta_snd
  have hgamma : p.gamma = eisensteinCoord p.gamma.fst p.gamma.snd := by
    rfl
  have hformula :
      p.gamma.fst ^ 3 - 3 * p.gamma.fst * p.gamma.snd ^ 2 -
          p.gamma.snd ^ 3 =
        3 * (q.powerSplit.A : ℤ) ^ 3 := by
    have hsecond' := hsecond
    rw [hsector, EisensteinUnitSector.rep, hgamma] at hsecond'
    simpa only [eisenstein_tau_sq_mul_cube_snd] using hsecond'
  have hdivformula :
      (3 : ℤ) ∣ p.gamma.fst ^ 3 - 3 * p.gamma.fst * p.gamma.snd ^ 2 -
          p.gamma.snd ^ 3 := by
    exact ⟨(q.powerSplit.A : ℤ) ^ 3, hformula⟩
  have hdivcube :
      (3 : ℤ) ∣ p.gamma.fst ^ 3 - p.gamma.snd ^ 3 := by
    refine ⟨(q.powerSplit.A : ℤ) ^ 3 +
      p.gamma.fst * p.gamma.snd ^ 2, ?_⟩
    calc
      p.gamma.fst ^ 3 - p.gamma.snd ^ 3 =
          (p.gamma.fst ^ 3 - 3 * p.gamma.fst * p.gamma.snd ^ 2 -
            p.gamma.snd ^ 3) + 3 * p.gamma.fst * p.gamma.snd ^ 2 := by ring
      _ = 3 * (q.powerSplit.A : ℤ) ^ 3 +
          3 * p.gamma.fst * p.gamma.snd ^ 2 := by rw [hformula]
      _ = 3 * ((q.powerSplit.A : ℤ) ^ 3 +
          p.gamma.fst * p.gamma.snd ^ 2) := by ring
  have hsub : (3 : ℤ) ∣ p.gamma.fst - p.gamma.snd :=
    three_dvd_sub_of_three_dvd_cube_sub hdivcube
  have hnormdiv : (3 : ℤ) ∣ norm p.gamma := by
    rw [show p.gamma = eisensteinCoord p.gamma.fst p.gamma.snd by rfl]
    exact three_dvd_eisenstein_norm_of_three_dvd_sub hsub
  have hBdiv : (3 : ℤ) ∣ (q.powerSplit.B : ℤ) := by
    simpa [EisensteinCubeSectorPacket.gamma_norm_eq_B p] using hnormdiv
  have hBNat : 3 ∣ q.powerSplit.B := by
    exact_mod_cast hBdiv
  exact q.powerSplit.three_not_dvd_B hBNat

/-- Every sector packet is forced into the one sector. -/
theorem sector_eq_one
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    p.sector = .one := by
  cases h : p.sector with
  | one => rfl
  | tau => exact (tau_sector_false p h).elim
  | tauSq => exact (tauSq_sector_false p h).elim

/-- The normalized beta is an exact cube. -/
theorem beta_eq_cube
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    p.cubeUpToUnit.conjugateCoprime.stripped.beta = p.gamma ^ 3 := by
  rw [p.beta_eq, sector_eq_one p, EisensteinUnitSector.rep]
  simp

/-- The coordinates of the exact cube satisfy `r*s*(r+s)=A^3`. -/
theorem gamma_coordinate_product_eq_A_cube
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    p.gamma.fst * p.gamma.snd * (p.gamma.fst + p.gamma.snd) =
      (p.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.A : ℤ) ^ 3 := by
  let q := p.cubeUpToUnit.conjugateCoprime.stripped
  have hsecond :
      (p.gamma ^ 3).snd = 3 * (q.powerSplit.A : ℤ) ^ 3 := by
    rw [← beta_eq_cube p]
    exact q.beta_snd
  have hgamma : p.gamma = eisensteinCoord p.gamma.fst p.gamma.snd := by
    rfl
  have hcube := eisenstein_cube_snd p.gamma.fst p.gamma.snd
  rw [hgamma] at hsecond
  rw [hcube] at hsecond
  nlinarith

/-- The coordinate form of the residual norm is `B`. -/
theorem gamma_coordinate_norm_eq_B
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    p.gamma.fst ^ 2 + p.gamma.fst * p.gamma.snd + p.gamma.snd ^ 2 =
      (p.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.B : ℤ) := by
  rw [← eisenstein_norm_coords p.gamma.fst p.gamma.snd]
  exact EisensteinCubeSectorPacket.gamma_norm_eq_B p

/-- An exact-cube packet ready for the next descent checkpoint. -/
structure EisensteinExactCubePacket
    (a b c : ℕ) : Type where
  sectorPacket : EisensteinCubeSectorPacket a b c
  sector_one : sectorPacket.sector = .one
  beta_eq_cube :
    sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.beta =
      sectorPacket.gamma ^ 3
  coordinate_product :
    sectorPacket.gamma.fst * sectorPacket.gamma.snd *
        (sectorPacket.gamma.fst + sectorPacket.gamma.snd) =
      (sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.A : ℤ) ^ 3
  coordinate_norm :
    norm sectorPacket.gamma =
      (sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.B : ℤ)

/-- Package the forced one-sector identities without another choice. -/
def eisensteinExactCubePacket_of_sectorPacket
    {a b c : ℕ} (p : EisensteinCubeSectorPacket a b c) :
    EisensteinExactCubePacket a b c :=
  { sectorPacket := p
    sector_one := sector_eq_one p
    beta_eq_cube := beta_eq_cube p
    coordinate_product := gamma_coordinate_product_eq_A_cube p
    coordinate_norm := EisensteinCubeSectorPacket.gamma_norm_eq_B p }

end DkMath.FLT.Three
