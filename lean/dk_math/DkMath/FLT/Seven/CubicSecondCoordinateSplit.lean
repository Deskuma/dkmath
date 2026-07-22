/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AwayValuationTransfer

#print "file: DkMath.FLT.Seven.CubicSecondCoordinateSplit"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

def seventhPowerSndLeftCubic (u v : ℤ) : ℤ :=
  u ^ 3 - 2 * u ^ 2 * v - u * v ^ 2 + v ^ 3

def seventhPowerSndRightCubic (u v : ℤ) : ℤ :=
  u ^ 3 + 5 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3

theorem seventhPowerSndCore_factor (u v : ℤ) :
    seventhPowerSndCore u v =
      seventhPowerSndLeftCubic u v * seventhPowerSndRightCubic u v := by
  simp [seventhPowerSndCore, seventhPowerSndLeftCubic,
    seventhPowerSndRightCubic]
  ring

theorem seventhPowerSnd_cubic_sub (u v : ℤ) :
    seventhPowerSndRightCubic u v - seventhPowerSndLeftCubic u v =
      7 * u * v * (u + v) := by
  simp [seventhPowerSndLeftCubic, seventhPowerSndRightCubic]
  ring

theorem seventhPowerSnd_cubic_add (u v : ℤ) :
    seventhPowerSndLeftCubic u v + seventhPowerSndRightCubic u v =
      (2 * u + v) * norm (⟨u, v⟩ : TraceOneInt (-2)) := by
  simp [seventhPowerSndLeftCubic, seventhPowerSndRightCubic,
    DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

theorem away_endpoint_product_cubic_load_eq {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) =
      7 * Int.natAbs p.root.snd *
        Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd) *
        Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd) := by
  rw [away_endpoint_product_load_eq p, seventhPowerSndCore_factor,
    Int.natAbs_mul]
  ring

theorem AwayCoordinateNormalForm.root_coordinates_isCoprime {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    IsCoprime p.root.fst p.root.snd := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqu : (q : ℤ) ∣ p.root.fst :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_left _ _)
  have hqv : (q : ℤ) ∣ p.root.snd :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_right _ _)
  rcases hqu with ⟨u, hu⟩
  rcases hqv with ⟨v, hv⟩
  have hqfst : (q : ℤ) ∣ seventhPowerFst p.root.fst p.root.snd := by
    refine ⟨q ^ 6 * (u ^ 7 - 42 * u ^ 5 * v ^ 2 - 70 * u ^ 4 * v ^ 3 +
      70 * u ^ 3 * v ^ 4 + 126 * u ^ 2 * v ^ 5 + 14 * u * v ^ 6 -
      10 * v ^ 7), ?_⟩
    simp [hu, hv, seventhPowerFst]
    ring
  have hqsnd : (q : ℤ) ∣ seventhPowerSnd p.root.fst p.root.snd := by
    refine ⟨q ^ 6 * (7 * u ^ 6 * v + 21 * u ^ 5 * v ^ 2 -
      35 * u ^ 4 * v ^ 3 - 105 * u ^ 3 * v ^ 4 -
      21 * u ^ 2 * v ^ 5 + 35 * u * v ^ 6 + 7 * v ^ 7), ?_⟩
    simp [hu, hv, seventhPowerSnd]
    ring
  have hcoords := counterexample_cyclotomicSeven_coordinates_isCoprime
    p.counterexample
  have hqA : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ) := by
    rw [p.fst_eq]
    exact hqfst
  have hqB : (q : ℤ) ∣ cyclotomicSevenSnd (z : ℤ) (y : ℤ) := by
    rw [p.snd_eq]
    exact hqsnd
  have hunit : IsUnit (q : ℤ) := hcoords.isUnit_of_dvd' hqA hqB
  rcases Int.isUnit_iff.mp hunit with hq1 | hqneg
  · exact hq.ne_one (by exact_mod_cast hq1)
  · have : (0 : ℤ) ≤ q := by positivity
    omega

theorem AwayCoordinateNormalForm.root_coordinates_natAbs_coprime {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime (Int.natAbs p.root.fst) (Int.natAbs p.root.snd) :=
  Int.isCoprime_iff_nat_coprime.mp p.root_coordinates_isCoprime

theorem AwayCoordinateNormalForm.leftCubic_ne_zero {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    seventhPowerSndLeftCubic p.root.fst p.root.snd ≠ 0 := by
  intro h
  apply p.sndCore_ne_zero
  rw [seventhPowerSndCore_factor, h, zero_mul]

theorem AwayCoordinateNormalForm.rightCubic_ne_zero {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    seventhPowerSndRightCubic p.root.fst p.root.snd ≠ 0 := by
  intro h
  apply p.sndCore_ne_zero
  rw [seventhPowerSndCore_factor, h, mul_zero]

theorem AwayCoordinateNormalForm.leftCubic_natAbs_pos {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    0 < Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd) :=
  Int.natAbs_pos.mpr p.leftCubic_ne_zero

theorem AwayCoordinateNormalForm.rightCubic_natAbs_pos {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    0 < Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd) :=
  Int.natAbs_pos.mpr p.rightCubic_ne_zero

theorem AwayCoordinateNormalForm.coprime_rootSnd_leftCubic {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd)) := by
  apply Int.isCoprime_iff_nat_coprime.mp
  have h := p.root_coordinates_isCoprime.pow_left (m := 3)
  have h' := h.add_mul_right_left
    (-2 * p.root.fst ^ 2 - p.root.fst * p.root.snd + p.root.snd ^ 2)
  convert h'.symm using 1
  all_goals simp [seventhPowerSndLeftCubic]
  all_goals ring

theorem AwayCoordinateNormalForm.coprime_rootSnd_rightCubic {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd)) := by
  apply Int.isCoprime_iff_nat_coprime.mp
  have h := p.root_coordinates_isCoprime.pow_left (m := 3)
  have h' := h.add_mul_right_left
    (5 * p.root.fst ^ 2 + 6 * p.root.fst * p.root.snd + p.root.snd ^ 2)
  convert h'.symm using 1
  all_goals simp [seventhPowerSndRightCubic]
  all_goals ring

theorem AwayCoordinateNormalForm.coprime_leftCubic_rightCubic {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime
      (Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd))
      (Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let u : ZMod q := p.root.fst
  let v : ZMod q := p.root.snd
  have hqL : (q : ℤ) ∣ seventhPowerSndLeftCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqR : (q : ℤ) ∣ seventhPowerSndRightCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hL :
      u ^ 3 - 2 * u ^ 2 * v - u * v ^ 2 + v ^ 3 = 0 := by
    simpa [u, v, seventhPowerSndLeftCubic] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqL
  have hR :
      u ^ 3 + 5 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3 = 0 := by
    simpa [u, v, seventhPowerSndRightCubic] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqR
  have hprimitive : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨hu, hv⟩
    rcases p.root_coordinates_isCoprime with ⟨a, b, hab⟩
    have hc := congrArg (fun n : ℤ => (n : ZMod q)) hab
    push_cast at hc
    simp [u, v, hu, hv] at hc
  have hfactor : (7 : ZMod q) * u * v * (u + v) = 0 := by
    linear_combination hR - hL
  have hqeq : q = 7 := by
    rcases mul_eq_zero.mp hfactor with huv | hsum
    · rcases mul_eq_zero.mp huv with h7u | hv
      · rcases mul_eq_zero.mp h7u with h7 | hu
        · have hq7 : q ∣ 7 :=
            (ZMod.natCast_eq_zero_iff 7 q).1 (by simpa using h7)
          exact (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7 |>.resolve_left hq.ne_one
        · have hv0 : v = 0 := by
            rw [hu] at hL
            have hv3 : v ^ 3 = 0 := by simpa using hL
            exact eq_zero_of_pow_eq_zero hv3
          exact False.elim (hprimitive ⟨hu, hv0⟩)
      · have hu0 : u = 0 := by
          rw [hv] at hL
          simpa using eq_zero_of_pow_eq_zero (by simpa using hL : u ^ 3 = 0)
        exact False.elim (hprimitive ⟨hu0, hv⟩)
    · have hu : u = -v := eq_neg_of_add_eq_zero_left hsum
      have hv0 : v = 0 := by
        rw [hu] at hL
        ring_nf at hL
        exact eq_zero_of_pow_eq_zero (neg_eq_zero.mp hL)
      exact False.elim (hprimitive ⟨by simp [hu, hv0], hv0⟩)
  subst q
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnorm0 :
      (norm p.root : ZMod 7) = 0 := by
    have hadd :
        ((2 : ZMod 7) * u + v) * (norm p.root : ZMod 7) = 0 := by
      have hc := congrArg (fun n : ℤ => (n : ZMod 7))
        (seventhPowerSnd_cubic_add p.root.fst p.root.snd)
      push_cast at hc
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqL,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqR] at hc
      simpa [u, v] using hc
    rcases mul_eq_zero.mp hadd with hlin | hn
    · have hlinear :
          (p.root.fst : ZMod 7) + 4 * (p.root.snd : ZMod 7) = 0 := by
        dsimp [u, v] at hlin
        calc
          _ = (8 : ZMod 7) * (p.root.fst : ZMod 7) +
              4 * (p.root.snd : ZMod 7) := by
            rw [show (8 : ZMod 7) = 1 by decide]
            ring
          _ = 4 * (2 * (p.root.fst : ZMod 7) + (p.root.snd : ZMod 7)) := by ring
          _ = 0 := by rw [hlin]; ring
      rw [traceOneNorm_mod_seven_eq_linear_sq, hlinear]
      norm_num
    · exact hn
  exact p.root_norm_not_seven_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hnorm0)

structure AwayRootCoprimeTriple (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  vPart : ℕ
  leftPart : ℕ
  rightPart : ℕ
  vPart_eq : vPart = Int.natAbs normal.root.snd
  leftPart_eq : leftPart = Int.natAbs
    (seventhPowerSndLeftCubic normal.root.fst normal.root.snd)
  rightPart_eq : rightPart = Int.natAbs
    (seventhPowerSndRightCubic normal.root.fst normal.root.snd)
  vPart_pos : 0 < vPart
  leftPart_pos : 0 < leftPart
  rightPart_pos : 0 < rightPart
  coprime_v_left : Nat.Coprime vPart leftPart
  coprime_v_right : Nat.Coprime vPart rightPart
  coprime_left_right : Nat.Coprime leftPart rightPart

def awayRootCoprimeTriple {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    AwayRootCoprimeTriple x y z where
  normal := p
  vPart := Int.natAbs p.root.snd
  leftPart := Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd)
  rightPart := Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd)
  vPart_eq := rfl
  leftPart_eq := rfl
  rightPart_eq := rfl
  vPart_pos := Int.natAbs_pos.mpr p.root_snd_ne_zero
  leftPart_pos := p.leftCubic_natAbs_pos
  rightPart_pos := p.rightCubic_natAbs_pos
  coprime_v_left := p.coprime_rootSnd_leftCubic
  coprime_v_right := p.coprime_rootSnd_rightCubic
  coprime_left_right := p.coprime_leftCubic_rightCubic

end DkMath.FLT.Seven
