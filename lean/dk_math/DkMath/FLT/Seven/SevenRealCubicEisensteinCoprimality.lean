/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicEisensteinCubeCertificate

#print "file: DkMath.FLT.Seven.SevenRealCubicEisensteinCoprimality"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open DkMath.FLT.Three
open DkMath.NumberTheory.TraceOneQuadratic
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

private theorem zmodNine_two_not_cube :
    ∀ x : ZMod 9, x ^ 3 ≠ 2 := by
  decide

theorem sourcePlaneNormSeven_three_not_dvd_q
    {a b q : ℤ}
    (hF : sourcePlaneNormSevenForm a b = -7)
    (hQ : sourcePlaneNormSevenQuadratic a b = 7 * q) :
    ¬(3 : ℤ) ∣ q := by
  intro hq
  have hQ3 : (3 : ℤ) ∣ sourcePlaneNormSevenQuadratic a b := by
    rw [hQ]
    exact dvd_mul_of_dvd_right hq 7
  have hdiff_sq : (3 : ℤ) ∣ (a - b) ^ 2 := by
    have hthree : (3 : ℤ) ∣ 3 * a * b := by
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_refl 3) a) b
    have hidentity : (a - b) ^ 2 =
        sourcePlaneNormSevenQuadratic a b - 3 * a * b := by
      simp [sourcePlaneNormSevenQuadratic]
      ring
    rw [hidentity]
    exact dvd_sub hQ3 hthree
  have hdiff : (3 : ℤ) ∣ a - b := by
    exact (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hdiff_sq
  rcases hdiff with ⟨d, hd⟩
  have ha : a = b + 3 * d := by
    linarith
  have hFsub : sourcePlaneNormSevenForm (b + 3 * d) b = -7 := by
    rw [← ha]
    exact hF
  have hidentity : sourcePlaneNormSevenForm (b + 3 * d) b =
      b ^ 3 + 9 * (2 * b ^ 2 * d + 5 * b * d ^ 2 + 3 * d ^ 3) := by
    simp [sourcePlaneNormSevenForm]
    ring
  have hmod9 : (9 : ℤ) ∣ b ^ 3 - 2 := by
    refine ⟨-(2 * b ^ 2 * d + 5 * b * d ^ 2 + 3 * d ^ 3 + 1), ?_⟩
    rw [hidentity] at hFsub
    nlinarith [hFsub]
  have hzero : ((b ^ 3 - 2 : ℤ) : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr hmod9
  push_cast at hzero
  apply zmodNine_two_not_cube (b : ZMod 9)
  linear_combination hzero

theorem sourcePlaneNormSeven_parameter_three_not_dvd_q
    {A m : ℤ}
    (hF : sourcePlaneNormSevenForm (2 * A - 21 * m) (-3 * A + 28 * m) = -7) :
    ¬(3 : ℤ) ∣ sourcePlaneNormSevenQParameter A m := by
  apply sourcePlaneNormSeven_three_not_dvd_q hF
  exact sourcePlaneNormSevenQuadratic_parameter A m

theorem eisenstein_current_q_coprime_s
    {q r s : ℤ}
    (hq_not_three : ¬(3 : ℤ) ∣ q)
    (hnorm : norm (eisensteinCoord r s) = q ^ 3)
    (hthree : 5 * r + 8 * s = 3) :
    IsCoprime q s := by
  rw [Int.isCoprime_iff_nat_coprime]
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpqNat : p ∣ q.natAbs := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpsNat : p ∣ s.natAbs := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  have hpq : (p : ℤ) ∣ q := Int.natCast_dvd.mpr hpqNat
  have hps : (p : ℤ) ∣ s := Int.natCast_dvd.mpr hpsNat
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpNorm : (p : ℤ) ∣ norm (eisensteinCoord r s) := by
    rw [hnorm]
    exact dvd_pow hpq (by decide : 3 ≠ 0)
  have hpR2 : (p : ℤ) ∣ r ^ 2 := by
    rw [eisenstein_norm_coords] at hpNorm
    have h := dvd_sub hpNorm
      (dvd_add (dvd_mul_of_dvd_right hps r) (dvd_pow hps (by decide : 2 ≠ 0)))
    simpa only [add_assoc, add_sub_cancel_right] using h
  have hpR : (p : ℤ) ∣ r := hpZ.dvd_of_dvd_pow hpR2
  have hpThree : (p : ℤ) ∣ 3 := by
    have hleft : (p : ℤ) ∣ 5 * r + 8 * s :=
      dvd_add (dvd_mul_of_dvd_right hpR 5) (dvd_mul_of_dvd_right hps 8)
    rwa [hthree] at hleft
  have hpThreeNat : p ∣ 3 := Int.natCast_dvd.mp hpThree
  rcases (Nat.dvd_prime Nat.prime_three).mp hpThreeNat with hp_one | hp_eq
  · exact hp.ne_one hp_one
  · exact hq_not_three (by simpa [hp_eq] using hpq)

private theorem eisenstein_current_norm_eq_one_of_unit
    {d : EisensteinInt} (hunit : IsUnit (norm d)) : norm d = 1 := by
  have hnat : (norm d).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hunit
  have hnonneg : 0 ≤ norm d := eisenstein_norm_nonneg d
  have hcast : ((norm d).natAbs : ℤ) = norm d := Int.natAbs_of_nonneg hnonneg
  rw [← hcast]
  exact_mod_cast hnat

theorem eisenstein_current_relPrime_conj
    {q r s : ℤ}
    (hq_not_three : ¬(3 : ℤ) ∣ q)
    (hnorm : norm (eisensteinCoord r s) = q ^ 3)
    (hthree : 5 * r + 8 * s = 3) :
    EisensteinRelPrime (eisensteinCoord r s) (conj (eisensteinCoord r s)) := by
  have hqs : IsCoprime q s := eisenstein_current_q_coprime_s hq_not_three hnorm hthree
  have hq3 : IsCoprime q (3 : ℤ) :=
    ((show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hq_not_three).symm
  have hqpow3_three : IsCoprime (q ^ 3) (3 : ℤ) := hq3.pow_left
  have hqpow3_squares : IsCoprime (q ^ 3) (s ^ 2) :=
    hqs.pow_left.pow_right
  have hcop : IsCoprime (q ^ 3) (3 * s ^ 2) :=
    hqpow3_three.mul_right hqpow3_squares
  intro d hd hdc
  have hddiff : d ∣ eisensteinCoord r s - conj (eisensteinCoord r s) :=
    dvd_sub hd hdc
  have hnormd : norm d ∣ q ^ 3 := by
    have h := eisenstein_norm_dvd_of_dvd hd
    rw [hnorm] at h
    exact h
  have hnormdiff : norm d ∣ 3 * s ^ 2 := by
    have h := eisenstein_norm_dvd_of_dvd hddiff
    rw [eisenstein_norm_sub_conj] at h
    simpa [eisensteinCoord] using h
  have hunitNorm : IsUnit (norm d) := hcop.isUnit_of_dvd' hnormd hnormdiff
  exact eisenstein_isUnit_of_norm_eq_one
    (eisenstein_current_norm_eq_one_of_unit hunitNorm)

structure EisensteinCurrentCubeSectorPacket where
  q : ℤ
  r : ℤ
  s : ℤ
  h : ℤ
  sector : EisensteinUnitSector
  gamma : EisensteinInt
  delta_eq : eisensteinCoord r s = sector.rep * gamma ^ 3
  gamma_norm : DkMath.NumberTheory.TraceOneQuadratic.norm gamma = q
  h_relation : h = 3 * r - 5 * s
  three_relation : 5 * r + 8 * s = 3
  r_near : (7 : ℤ) ^ 8 ∣ r + 1
  s_near : (7 : ℤ) ^ 8 ∣ s - 1

private theorem int_cube_injective_on_nonnegative
    {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ^ 3 = y ^ 3) :
    x = y := by
  have hfactor : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
    calc
      (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 := by ring
      _ = 0 := sub_eq_zero.mpr hxy
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

theorem eisenstein_current_cube_sector_packet
    {q r s : ℤ}
    (hrel : EisensteinRelPrime (eisensteinCoord r s)
      (conj (eisensteinCoord r s)))
    (hnorm : norm (eisensteinCoord r s) = q ^ 3)
    {h : ℤ}
    (hh : h = 3 * r - 5 * s)
    (hthree : 5 * r + 8 * s = 3)
    (hr_near : (7 : ℤ) ^ 8 ∣ r + 1)
    (hs_near : (7 : ℤ) ^ 8 ∣ s - 1) :
    ∃ packet : EisensteinCurrentCubeSectorPacket,
      packet.q = q ∧ packet.r = r ∧ packet.s = s := by
  obtain ⟨sector, gamma, hEq⟩ := eisenstein_sector_cube_normalization hrel hnorm
  have hnormGammaCube : norm gamma ^ 3 = q ^ 3 := by
    calc
      norm gamma ^ 3 = DkMath.NumberTheory.TraceOneQuadratic.norm
          (sector.rep * gamma ^ 3) := by
        rw [eisenstein_norm_mul, sector.rep_norm,
          DkMath.Lib.NumberTheory.traceOne_norm_pow]
        ring
      _ = norm (eisensteinCoord r s) := by rw [← hEq]
      _ = q ^ 3 := hnorm
  have hq_nonneg : 0 ≤ q := by
    by_contra hq
    have hqneg : q < 0 := lt_of_not_ge hq
    have hqcube_neg : q ^ 3 < 0 := by
      nlinarith [sq_pos_of_neg hqneg]
    have hnorm_nonneg : 0 ≤ norm gamma := eisenstein_norm_nonneg gamma
    have hnormcube_nonneg : 0 ≤ norm gamma ^ 3 := pow_nonneg hnorm_nonneg 3
    have hnormcube_neg : norm gamma ^ 3 < 0 := by
      rw [hnormGammaCube]
      exact hqcube_neg
    exact (not_lt_of_ge hnormcube_nonneg) hnormcube_neg
  have hnormGamma : norm gamma = q :=
    int_cube_injective_on_nonnegative (eisenstein_norm_nonneg gamma) hq_nonneg
      hnormGammaCube
  refine ⟨⟨q, r, s, h, sector, gamma, hEq, hnormGamma,
    hh, hthree, hr_near, hs_near⟩, rfl, rfl, rfl⟩

private theorem zmodSeven_one_second_impossible :
    ∀ R S : ZMod 7,
      5 * (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) +
          8 * (3 * R * S * (R + S)) ≠ 3 := by
  decide

private theorem zmodSeven_tau_second_impossible :
    ∀ R S : ZMod 7,
      8 * (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) +
          3 * (3 * R * S * (R + S)) ≠ 3 := by
  decide

theorem eisenstein_current_sector_eq_tauSq
    {h r s : ℤ} {sector : EisensteinUnitSector} {gamma : EisensteinInt}
    (hh : h = 3 * r - 5 * s)
    (hthree : 5 * r + 8 * s = 3)
    (hEq : eisensteinCoord r s = sector.rep * gamma ^ 3) :
    sector = .tauSq := by
  rcases gamma with ⟨R, S⟩
  have hz : eisensteinCoord h 3 =
      eisensteinPiSeven ^ 2 * sector.rep * (eisensteinCoord R S) ^ 3 := by
    calc
      eisensteinCoord h 3 =
          eisensteinPiSeven ^ 2 * eisensteinCoord r s :=
        eisensteinPiSeven_sq_mul_coordinate h r s hh hthree.symm
      _ = eisensteinPiSeven ^ 2 * sector.rep * (eisensteinCoord R S) ^ 3 := by
        rw [hEq]
        simp only [eisensteinCoord]
        rw [mul_assoc]
  have hsecond := congrArg (fun x : EisensteinInt => x.snd) hz
  rw [eisenstein_sector_second_coordinate] at hsecond
  have hmod := congrArg (fun x : ℤ => (x : ZMod 7)) hsecond
  cases sector with
  | one =>
      norm_num [eisensteinCoord, eisensteinCubeFirstCoordinate,
        eisensteinCubeSecondCoordinate] at hmod
      exact False.elim
        (zmodSeven_one_second_impossible (R : ZMod 7) (S : ZMod 7) hmod.symm)
  | tau =>
      norm_num [eisensteinCoord, eisensteinCubeFirstCoordinate,
        eisensteinCubeSecondCoordinate] at hmod
      exact False.elim
        (zmodSeven_tau_second_impossible (R : ZMod 7) (S : ZMod 7) hmod.symm)
  | tauSq => rfl

theorem EisensteinCurrentCubeSectorPacket.sector_eq_tauSq
    (packet : EisensteinCurrentCubeSectorPacket) :
    packet.sector = .tauSq :=
  eisenstein_current_sector_eq_tauSq packet.h_relation packet.three_relation
    packet.delta_eq

theorem eisenstein_current_tauSq_FiveEquation
    {R S : ℤ}
    (hsecond :
      3 * (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) -
          5 * (3 * R * S * (R + S)) = 3) :
    R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 = 1 := by
  nlinarith [hsecond]

end SevenRealCubic
end
end DkMath.FLT.Seven
