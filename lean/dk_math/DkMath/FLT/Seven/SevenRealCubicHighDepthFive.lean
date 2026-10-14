/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicEisensteinCoprimality

#print "file: DkMath.FLT.Seven.SevenRealCubicHighDepthFive"

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

private theorem current_near_parameter_exists
    {r s : ℤ}
    (hthree : 5 * r + 8 * s = 3)
    (hr : (7 : ℤ) ^ 8 ∣ r + 1)
    (hs : (7 : ℤ) ^ 8 ∣ s - 1) :
    ∃ T : ℤ, r = -1 + 8 * T ∧ s = 1 - 5 * T ∧
      (7 : ℤ) ^ 8 ∣ T := by
  rcases hr with ⟨u, hu⟩
  rcases hs with ⟨v, hv⟩
  have huv : 5 * u + 8 * v = 0 := by
    nlinarith [hthree, hu, hv]
  have h8mul : (8 : ℤ) ∣ 5 * u := by
    refine ⟨-v, ?_⟩
    nlinarith [huv]
  have h8u : (8 : ℤ) ∣ u :=
    (by norm_num : IsCoprime (8 : ℤ) 5).dvd_of_dvd_mul_left h8mul
  rcases h8u with ⟨k, huk⟩
  have hvk : v = -5 * k := by
    nlinarith [huv, huk]
  refine ⟨7 ^ 8 * k, ?_, ?_, ?_⟩
  · nlinarith [hu, huk]
  · nlinarith [hv, hvk]
  · exact ⟨k, by ring⟩

structure EisensteinCurrentHighDepthFivePacket where
  source : EisensteinCurrentCubeSectorPacket
  R : ℤ
  S : ℤ
  T : ℤ
  five_eq : R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 = 1
  q_norm : R ^ 2 + R * S + S ^ 2 = source.q
  q_pos : 0 < source.q
  r_eq : source.r = -1 + 8 * T
  s_eq : source.s = 1 - 5 * T
  T_eq : T = -R * S * (R + S)
  T_depth : (7 : ℤ) ^ 8 ∣ T
  q_cube : source.q ^ 3 = 49 * T ^ 2 - 13 * T + 1

private theorem current_tauSq_coordinate_transport
    {r s R S : ℤ}
    (hEq : eisensteinCoord r s = eisensteinTau ^ 2 *
      (eisensteinCoord R S) ^ 3) :
    r = -(R ^ 3 - 3 * R * S ^ 2 - S ^ 3) -
        3 * R * S * (R + S) ∧
      s = R ^ 3 - 3 * R * S ^ 2 - S ^ 3 := by
  have hEq' := hEq
  rw [eisenstein_tau_sq, eisenstein_cube_coords] at hEq'
  have hfst := congrArg (fun x : EisensteinInt => x.fst) hEq'
  have hsnd := congrArg (fun x : EisensteinInt => x.snd) hEq'
  simp [eisensteinCoord, eisensteinTau, tau] at hfst hsnd
  constructor <;> nlinarith

theorem eisenstein_current_highDepthFivePacket_of_source
    (packet : EisensteinCurrentCubeSectorPacket)
    (hq_pos : 0 < packet.q) :
    ∃ high : EisensteinCurrentHighDepthFivePacket,
      high.source = packet := by
  have hsector : packet.sector = .tauSq := packet.sector_eq_tauSq
  have hparam : ∃ T : ℤ, packet.r = -1 + 8 * T ∧
      packet.s = 1 - 5 * T ∧ (7 : ℤ) ^ 8 ∣ T :=
    current_near_parameter_exists packet.three_relation packet.r_near packet.s_near
  let R : ℤ := packet.gamma.fst
  let S : ℤ := packet.gamma.snd
  have hgamma : packet.gamma = eisensteinCoord R S := by
    rfl
  rcases hparam with ⟨T, hr, hs, hT⟩
  have hdelta : eisensteinCoord packet.r packet.s =
      eisensteinTau ^ 2 * (eisensteinCoord R S) ^ 3 := by
    have hdelta' := packet.delta_eq
    rw [hsector, EisensteinUnitSector.rep, hgamma] at hdelta'
    exact hdelta'
  have htransport := current_tauSq_coordinate_transport hdelta
  have hX : R ^ 3 - 3 * R * S ^ 2 - S ^ 3 = 1 - 5 * T := by
    nlinarith [htransport.2, hs]
  have hY : 3 * R * S * (R + S) = -3 * T := by
    nlinarith [htransport.1, htransport.2, hr, hs]
  have hT_eq : T = -R * S * (R + S) := by
    nlinarith [hY]
  have hfive : R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 = 1 := by
    have hsecond : 3 * (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) -
        5 * (3 * R * S * (R + S)) = 3 := by
      nlinarith [packet.three_relation, htransport.1, htransport.2]
    exact eisenstein_current_tauSq_FiveEquation hsecond
  have hqnorm : R ^ 2 + R * S + S ^ 2 = packet.q := by
    have hqnorm' := packet.gamma_norm
    rw [hgamma, eisenstein_norm_coords] at hqnorm'
    exact hqnorm'
  have hnorm_delta : norm (eisensteinCoord packet.r packet.s) = packet.q ^ 3 := by
    rw [packet.delta_eq, eisenstein_norm_mul, packet.sector.rep_norm,
      DkMath.Lib.NumberTheory.traceOne_norm_pow, packet.gamma_norm]
    simp only [one_mul]
  have hqcube : packet.q ^ 3 = 49 * T ^ 2 - 13 * T + 1 := by
    calc
      packet.q ^ 3 = norm (eisensteinCoord packet.r packet.s) := hnorm_delta.symm
      _ = norm (eisensteinCoord (-
          (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) -
            3 * R * S * (R + S))
          (R ^ 3 - 3 * R * S ^ 2 - S ^ 3)) := by
        have hcoord : eisensteinCoord packet.r packet.s =
            eisensteinCoord (-
              (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) -
                3 * R * S * (R + S))
              (R ^ 3 - 3 * R * S ^ 2 - S ^ 3) := by
          ext <;> simp [eisensteinCoord, htransport.1, htransport.2]
        rw [hcoord]
      _ = 49 * T ^ 2 - 13 * T + 1 := by
        rw [eisenstein_norm_coords]
        rw [hX, hY]
        ring
  let high : EisensteinCurrentHighDepthFivePacket :=
    { source := packet
      R := R
      S := S
      T := T
      five_eq := hfive
      q_norm := hqnorm
      q_pos := hq_pos
      r_eq := hr
      s_eq := hs
      T_eq := hT_eq
      T_depth := hT
      q_cube := hqcube }
  exact ⟨high, rfl⟩

private theorem isCoprime_RS_of_five_eq_one
    {R S : ℤ}
    (hfive : R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 = 1) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpRnat : p ∣ R.natAbs := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpSnat : p ∣ S.natAbs := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  have hpR : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpRnat
  have hpS : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpSnat
  have hpF : (p : ℤ) ∣
      R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 := by
    refine dvd_sub (dvd_sub (dvd_sub (dvd_pow hpR (by decide : 3 ≠ 0)) ?_) ?_) ?_
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_right hpS (5 * R ^ 2)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_left hpR (8 * S ^ 2)
    · exact dvd_pow hpS (by decide : 3 ≠ 0)
  have hpone_dvd : (p : ℤ) ∣ 1 := by
    rw [← hfive]
    exact hpF
  have hpone : IsUnit (p : ℤ) := isUnit_of_dvd_one hpone_dvd
  exact (Nat.prime_iff_prime_int.mp hp).not_isUnit hpone

theorem eisenstein_current_highDepthFive_pairwise_coprime
    {R S : ℤ}
    (hfive : R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3 = 1) :
    IsCoprime R S ∧ IsCoprime R (R + S) ∧ IsCoprime S (R + S) := by
  have hRS : IsCoprime R S := isCoprime_RS_of_five_eq_one hfive
  have hRsum : IsCoprime R (R + S) := by
    simpa [add_comm, add_left_comm, add_assoc] using hRS.add_mul_left_right 1
  have hSsum : IsCoprime S (R + S) := by
    simpa [add_comm, add_left_comm, add_assoc] using hRS.symm.add_mul_left_right 1
  exact ⟨hRS, hRsum, hSsum⟩

theorem eisenstein_current_highDepthFive_deep_factor
    {R S : ℤ}
    (hcop : IsCoprime R S ∧ IsCoprime R (R + S) ∧ IsCoprime S (R + S))
    (hdepth : (7 : ℤ) ^ 8 ∣ R * S * (R + S)) :
    ((7 : ℤ) ^ 8 ∣ R ∧ ¬(7 : ℤ) ∣ S ∧ ¬(7 : ℤ) ∣ R + S) ∨
      ((7 : ℤ) ^ 8 ∣ S ∧ ¬(7 : ℤ) ∣ R ∧ ¬(7 : ℤ) ∣ R + S) ∨
      ((7 : ℤ) ^ 8 ∣ R + S ∧ ¬(7 : ℤ) ∣ R ∧ ¬(7 : ℤ) ∣ S) := by
  have hp : Prime (7 : ℤ) := by norm_num
  have hp_prod : (7 : ℤ) ∣ R * S * (R + S) :=
    dvd_trans (dvd_pow_self (7 : ℤ) (by norm_num : 8 ≠ 0)) hdepth
  rcases hp.dvd_mul.mp hp_prod with hpR | hpSsum
  · rcases hp.dvd_mul.mp hpR with hpR | hpS
    · have hnotS : ¬(7 : ℤ) ∣ S := by
        intro h7
        exact hp.not_isUnit (hcop.1.isUnit_of_dvd' hpR h7)
      have hnotSum : ¬(7 : ℤ) ∣ R + S := by
        intro h7
        exact hp.not_isUnit (hcop.2.1.isUnit_of_dvd' hpR h7)
      have h7S : IsCoprime (7 : ℤ) S := hp.coprime_iff_not_dvd.mpr hnotS
      have h7Sum : IsCoprime (7 : ℤ) (R + S) :=
        hp.coprime_iff_not_dvd.mpr hnotSum
      have h7rest : IsCoprime ((7 : ℤ) ^ 8) (S * (R + S)) :=
        (h7S.pow_left).mul_right (h7Sum.pow_left)
      have hdepth' : (7 : ℤ) ^ 8 ∣ R * (S * (R + S)) := by
        simpa [mul_assoc] using hdepth
      exact Or.inl ⟨h7rest.dvd_of_dvd_mul_right hdepth', hnotS, hnotSum⟩
    · have hnotR : ¬(7 : ℤ) ∣ R := by
        intro h7
        exact hp.not_isUnit (hcop.1.isUnit_of_dvd' h7 hpS)
      have hnotSum : ¬(7 : ℤ) ∣ R + S := by
        intro h7
        exact hp.not_isUnit (hcop.2.2.isUnit_of_dvd' hpS h7)
      have h7R : IsCoprime (7 : ℤ) R := hp.coprime_iff_not_dvd.mpr hnotR
      have h7Sum : IsCoprime (7 : ℤ) (R + S) :=
        hp.coprime_iff_not_dvd.mpr hnotSum
      have h7rest : IsCoprime ((7 : ℤ) ^ 8) (R * (R + S)) :=
        (h7R.pow_left).mul_right (h7Sum.pow_left)
      have hdepth' : (7 : ℤ) ^ 8 ∣ S * (R * (R + S)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hdepth
      exact Or.inr (Or.inl ⟨h7rest.dvd_of_dvd_mul_right hdepth', hnotR, hnotSum⟩)
  · have hnotR : ¬(7 : ℤ) ∣ R := by
      intro h7
      exact hp.not_isUnit (hcop.2.1.isUnit_of_dvd' h7 hpSsum)
    have hnotS : ¬(7 : ℤ) ∣ S := by
      intro h7
      exact hp.not_isUnit (hcop.2.2.isUnit_of_dvd' h7 hpSsum)
    have h7R : IsCoprime (7 : ℤ) R := hp.coprime_iff_not_dvd.mpr hnotR
    have h7S : IsCoprime (7 : ℤ) S := hp.coprime_iff_not_dvd.mpr hnotS
    have h7rest : IsCoprime ((7 : ℤ) ^ 8) (R * S) :=
      (h7R.pow_left).mul_right (h7S.pow_left)
    have hdepth' : (7 : ℤ) ^ 8 ∣ (R * S) * (R + S) := hdepth
    exact Or.inr (Or.inr ⟨h7rest.dvd_of_dvd_mul_left hdepth', hnotR, hnotS⟩)

def sigma5 (p : ℤ × ℤ) : ℤ × ℤ := (-p.1 - p.2, p.1)

def F5 (R S : ℤ) : ℤ :=
  R ^ 3 - 5 * R ^ 2 * S - 8 * R * S ^ 2 - S ^ 3

def Q5 (R S : ℤ) : ℤ := R ^ 2 + R * S + S ^ 2

def T5 (R S : ℤ) : ℤ := R * S * (R + S)

theorem sigma5_three (R S : ℤ) :
    sigma5 (sigma5 (sigma5 (R, S))) = (R, S) := by
  ext <;> dsimp [sigma5] <;> ring

theorem sigma5_F5_invariant (R S : ℤ) :
    F5 (-R - S) R = F5 R S := by
  simp [F5]
  ring

theorem sigma5_Q5_invariant (R S : ℤ) :
    Q5 (-R - S) R = Q5 R S := by
  simp [Q5]
  ring

theorem sigma5_T5_invariant (R S : ℤ) :
    T5 (-R - S) R = T5 R S := by
  simp [T5]
  ring

theorem eisenstein_current_highDepthFive_deepS_identity (R S : ℤ) :
    F5 R S = (R + 3 * S) ^ 3 -
      7 * S * (2 * R ^ 2 + 5 * R * S + 4 * S ^ 2) := by
  simp [F5]
  ring

theorem eisenstein_current_highDepthFive_deepS_factorization
    {R S : ℤ} (hfive : F5 R S = 1) :
    (R + 3 * S) ^ 3 - 1 =
      7 * S * (2 * R ^ 2 + 5 * R * S + 4 * S ^ 2) ∧
    (R + 3 * S - 1) *
        ((R + 3 * S) ^ 2 + (R + 3 * S) + 1) =
      7 * S * (2 * R ^ 2 + 5 * R * S + 4 * S ^ 2) := by
  constructor
  · have hid := eisenstein_current_highDepthFive_deepS_identity R S
    nlinarith [hid, hfive]
  · calc
      (R + 3 * S - 1) * ((R + 3 * S) ^ 2 + (R + 3 * S) + 1) =
          (R + 3 * S) ^ 3 - 1 := by ring
      _ = 7 * S * (2 * R ^ 2 + 5 * R * S + 4 * S ^ 2) := by
        have hid := eisenstein_current_highDepthFive_deepS_identity R S
        nlinarith [hid, hfive]

theorem eisenstein_current_highDepthFive_deepS_factor_gcd_dvd_three
    (R S : ℤ) :
    ((Int.gcd (R + 3 * S - 1)
      ((R + 3 * S) ^ 2 + (R + 3 * S) + 1) : ℕ) : ℤ) ∣ 3 := by
  let A : ℤ := R + 3 * S
  have hleft : ((Int.gcd (A - 1) (A ^ 2 + A + 1) : ℕ) : ℤ) ∣ A - 1 :=
    Int.gcd_dvd_left _ _
  have hright : ((Int.gcd (A - 1) (A ^ 2 + A + 1) : ℕ) : ℤ) ∣ A ^ 2 + A + 1 :=
    Int.gcd_dvd_right _ _
  have hthree : ((Int.gcd (A - 1) (A ^ 2 + A + 1) : ℕ) : ℤ) ∣
      (A ^ 2 + A + 1) - (A + 2) * (A - 1) :=
    dvd_sub hright (dvd_mul_of_dvd_right hleft (A + 2))
  have hthree' : ((Int.gcd (A - 1) (A ^ 2 + A + 1) : ℕ) : ℤ) ∣ 3 := by
    convert hthree using 1
    ring
  simpa [A] using hthree'

theorem eisenstein_current_highDepthFive_deepS_cube_root_mod_seven
    {R S : ℤ} (hfive : F5 R S = 1) (hS : (7 : ℤ) ∣ S) :
    ((R : ZMod 7) ^ 3 = 1) ∧
      ((R : ZMod 7) = 1 ∨ (R : ZMod 7) = 2 ∨ (R : ZMod 7) = 4) := by
  have hSzero : (S : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd S 7).mpr hS
  have hmod := congrArg (fun x : ℤ => (x : ZMod 7)) hfive
  have hcube : (R : ZMod 7) ^ 3 = 1 := by
    simpa [F5, hSzero] using hmod
  have hroots : ∀ x : ZMod 7, x ^ 3 = 1 →
      x = 1 ∨ x = 2 ∨ x = 4 := by decide
  exact ⟨hcube, hroots _ hcube⟩

private theorem highDepth_int_cube_eq_one_iff (x : ℤ) : x ^ 3 = 1 ↔ x = 1 := by
  constructor
  · intro h
    have hfactor : (x - 1) * (x ^ 2 + x + 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · nlinarith [sq_nonneg x]
  · intro h
    subst x
    norm_num

theorem EisensteinCurrentHighDepthFivePacket.q_eq_one_iff_T_eq_zero
    (packet : EisensteinCurrentHighDepthFivePacket) :
    packet.source.q = 1 ↔ packet.T = 0 := by
  constructor
  · intro hq
    have hprod : packet.T * (49 * packet.T - 13) = 0 := by
      calc
        packet.T * (49 * packet.T - 13) =
            49 * packet.T ^ 2 - 13 * packet.T := by ring
        _ = 0 := by
          have hcube := packet.q_cube
          rw [hq] at hcube
          nlinarith [hcube]
    rcases mul_eq_zero.mp hprod with hT | hT
    · exact hT
    · exfalso
      omega
  · intro hT
    have hcube : packet.source.q ^ 3 = (1 : ℤ) ^ 3 := by
      simpa [hT] using packet.q_cube
    exact (highDepth_int_cube_eq_one_iff packet.source.q).mp hcube

theorem EisensteinCurrentHighDepthFivePacket.q_eq_one_iff_product_eq_zero
    (packet : EisensteinCurrentHighDepthFivePacket) :
    packet.source.q = 1 ↔ packet.R * packet.S * (packet.R + packet.S) = 0 := by
  rw [packet.q_eq_one_iff_T_eq_zero]
  constructor
  · intro h
    rw [packet.T_eq] at h
    nlinarith
  · intro h
    rw [packet.T_eq]
    nlinarith

private theorem int_cube_eq_one_iff (x : ℤ) : x ^ 3 = 1 ↔ x = 1 := by
  constructor
  · intro h
    have hfactor : (x - 1) * (x ^ 2 + x + 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · nlinarith [sq_nonneg x]
  · intro h
    subst x
    norm_num

private theorem int_cube_eq_neg_one_iff (x : ℤ) : x ^ 3 = -1 ↔ x = -1 := by
  constructor
  · intro h
    have hneg : (-x) ^ 3 = 1 := by nlinarith [h]
    have := (int_cube_eq_one_iff (-x)).mp hneg
    omega
  · intro h
    simp [h]

theorem eisenstein_current_highDepthFive_trivial_shell
    {R S : ℤ} (hfive : F5 R S = 1)
    (hzero : R * S * (R + S) = 0) :
    (R = 1 ∧ S = 0) ∨ (R = 0 ∧ S = -1) ∨ (R = -1 ∧ S = 1) := by
  rcases mul_eq_zero.mp hzero with hR | hsum
  · rcases mul_eq_zero.mp hR with hR | hS
    · right
      left
      have hcube : S ^ 3 = -1 := by
        simp [F5, hR] at hfive
        nlinarith [hfive]
      exact ⟨hR, (int_cube_eq_neg_one_iff S).mp hcube⟩
    · left
      have hcube : R ^ 3 = 1 := by
        simp [F5, hS] at hfive
        nlinarith [hfive]
      exact ⟨(int_cube_eq_one_iff R).mp hcube, hS⟩
  · right
    have hS : S = -R := by linarith
    rw [hS] at hfive
    have hcube : (-R) ^ 3 = 1 := by
      change R ^ 3 - 5 * R ^ 2 * (-R) - 8 * R * (-R) ^ 2 -
        (-R) ^ 3 = 1 at hfive
      nlinarith [hfive]
    have hR : R = -1 := by
      have hneg := (int_cube_eq_one_iff (-R)).mp hcube
      omega
    have hS' : S = 1 := by omega
    exact Or.inr ⟨hR, hS'⟩

theorem eisenstein_current_highDepthFive_trivial_shell_Q5
    {R S : ℤ} (h : (R = 1 ∧ S = 0) ∨
      (R = 0 ∧ S = -1) ∨ (R = -1 ∧ S = 1)) :
    Q5 R S = 1 := by
  rcases h with h | h | h <;> simp [Q5, h.1, h.2]

def n5 (R S : ℤ) : ℤ := 5 + 49 * R * S * (R + S)

theorem n5_eq_five_sub_49_T5 (R S : ℤ) :
    n5 R S = 5 - 49 * (-T5 R S) := by
  simp [n5, T5]
  ring

theorem eisenstein_current_highDepthFive_n5_eq_five_sub_49_T
    (packet : EisensteinCurrentHighDepthFivePacket) :
    n5 packet.R packet.S = 5 - 49 * packet.T := by
  simp [n5, packet.T_eq]
  ring

theorem eisenstein_current_highDepthFive_n5_depth
    (packet : EisensteinCurrentHighDepthFivePacket) :
    (7 : ℤ) ^ 10 ∣ n5 packet.R packet.S - 5 := by
  rw [eisenstein_current_highDepthFive_n5_eq_five_sub_49_T]
  have hpow : (7 : ℤ) ^ 10 = 49 * (7 : ℤ) ^ 8 := by norm_num
  have hdiv : (7 : ℤ) ^ 10 ∣ 49 * packet.T := by
    rw [hpow]
    rcases packet.T_depth with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  rcases hdiv with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  nlinarith [hk]

theorem eisenstein_current_highDepthFive_n5_eq_five_iff_T_eq_zero
    (packet : EisensteinCurrentHighDepthFivePacket) :
    n5 packet.R packet.S = 5 ↔ packet.T = 0 := by
  rw [eisenstein_current_highDepthFive_n5_eq_five_sub_49_T]
  constructor <;> intro h
  · nlinarith
  · simp [h]

end SevenRealCubic
end
end DkMath.FLT.Seven
