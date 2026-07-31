/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.DescentClosureAudit

#print "file: DkMath.FLT.Seven.FirstCoordinateRemainders"

namespace DkMath.FLT.Seven

theorem cyclotomicSevenFst_sub_right_cube (z y : ℤ) :
    cyclotomicSevenFst z y - z ^ 3 = y * (z - y) * (z + y) := by
  simp [cyclotomicSevenFst]
  ring

theorem cyclotomicSevenFst_add_left_cube (z y : ℤ) :
    cyclotomicSevenFst z y + y ^ 3 = z ^ 2 * (z + y) := by
  simp [cyclotomicSevenFst]
  ring

theorem leftEndpoint_dvd_fst_sub_right_cube (z y : ℤ) :
    y ∣ cyclotomicSevenFst z y - z ^ 3 := by
  rw [cyclotomicSevenFst_sub_right_cube]
  exact ⟨(z - y) * (z + y), by ring⟩

theorem rightEndpoint_dvd_fst_add_left_cube (z y : ℤ) :
    z ∣ cyclotomicSevenFst z y + y ^ 3 := by
  rw [cyclotomicSevenFst_add_left_cube]
  exact dvd_mul_of_dvd_left (dvd_pow_self z (by omega)) _

theorem endpointSum_dvd_fst_add_left_cube (z y : ℤ) :
    z + y ∣ cyclotomicSevenFst z y + y ^ 3 := by
  rw [cyclotomicSevenFst_add_left_cube]
  exact dvd_mul_left _ _

def seventhPowerFstVResidual (u v : ℤ) : ℤ :=
  -42 * u ^ 5 - 70 * u ^ 4 * v + 70 * u ^ 3 * v ^ 2 +
    126 * u ^ 2 * v ^ 3 + 14 * u * v ^ 4 - 10 * v ^ 5

theorem seventhPowerFst_eq_u_seven_add_v_sq (u v : ℤ) :
    seventhPowerFst u v = u ^ 7 + v ^ 2 * seventhPowerFstVResidual u v := by
  simp [seventhPowerFst, seventhPowerFstVResidual]
  ring

theorem rootSnd_dvd_fst_sub_u_seven (u v : ℤ) :
    v ∣ seventhPowerFst u v - u ^ 7 := by
  rw [seventhPowerFst_eq_u_seven_add_v_sq]
  exact ⟨v * seventhPowerFstVResidual u v, by ring⟩

theorem rootSnd_sq_dvd_fst_sub_u_seven (u v : ℤ) :
    v ^ 2 ∣ seventhPowerFst u v - u ^ 7 := by
  rw [seventhPowerFst_eq_u_seven_add_v_sq]
  exact ⟨seventhPowerFstVResidual u v, by ring⟩

def leftFstQuotient (u v : ℤ) : ℤ :=
  u ^ 4 + 2 * u ^ 3 * v - 37 * u ^ 2 * v ^ 2 -
    143 * u * v ^ 3 - 255 * v ^ 4

def leftFstCorrection (u v : ℤ) : ℤ :=
  10 * u ^ 2 + 2 * u * v - 5 * v ^ 2

theorem seventhPowerFst_leftCubic_division (u v : ℤ) :
    seventhPowerFst u v =
      seventhPowerSndLeftCubic u v * leftFstQuotient u v -
        49 * v ^ 5 * leftFstCorrection u v := by
  simp [seventhPowerFst, seventhPowerSndLeftCubic, leftFstQuotient,
    leftFstCorrection]
  ring

theorem leftCubic_dvd_fst_add_correction (u v : ℤ) :
    seventhPowerSndLeftCubic u v ∣
      seventhPowerFst u v + 49 * v ^ 5 * leftFstCorrection u v := by
  rw [seventhPowerFst_leftCubic_division]
  exact ⟨leftFstQuotient u v, by ring⟩

def rightFstQuotient (u v : ℤ) : ℤ :=
  u ^ 4 - 5 * u ^ 3 * v - 23 * u ^ 2 * v ^ 2 +
    74 * u * v ^ 3 - 157 * v ^ 4

def rightFstCorrection (u v : ℤ) : ℤ :=
  10 * u ^ 2 + 18 * u * v + 3 * v ^ 2

theorem seventhPowerFst_rightCubic_division (u v : ℤ) :
    seventhPowerFst u v =
      seventhPowerSndRightCubic u v * rightFstQuotient u v +
        49 * v ^ 5 * rightFstCorrection u v := by
  simp [seventhPowerFst, seventhPowerSndRightCubic, rightFstQuotient,
    rightFstCorrection]
  ring

theorem rightCubic_dvd_fst_sub_correction (u v : ℤ) :
    seventhPowerSndRightCubic u v ∣
      seventhPowerFst u v - 49 * v ^ 5 * rightFstCorrection u v := by
  rw [seventhPowerFst_rightCubic_division]
  exact ⟨rightFstQuotient u v, by ring⟩

def awayRootLinearModSeven {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ModSeven :=
  (p.root.fst : ModSeven) + 4 * (p.root.snd : ModSeven)

inductive AwayRootResidueSector (x y z : ℕ)
    (p : AwayCoordinateNormalForm x y z) : Prop
  | yCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = 0) (hz : (z : ModSeven) = t)
      (hx : (x : ModSeven) = t)
      (hroot : awayRootLinearModSeven p = t ^ 3)
  | zCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = t) (hz : (z : ModSeven) = 0)
      (hx : (x : ModSeven) = -t)
      (hroot : awayRootLinearModSeven p = -t ^ 3)
  | sumCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = t) (hz : (z : ModSeven) = -t)
      (hx : (x : ModSeven) = -2 * t)
      (hroot : awayRootLinearModSeven p = -t ^ 3)

theorem awayRootResidueSector_of_packet {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    AwayRootResidueSector x y z p := by
  have hlin := fermat7Equation_modSeven_linear p.counterexample.hEq
  have hfst :
      (cyclotomicSevenFst (z : ℤ) (y : ℤ) : ModSeven) =
        awayRootLinearModSeven p := by
    rw [p.fst_eq, seventhPowerFst_mod_seven]
    rfl
  cases awayExceptionalFactor_of_packet p with
  | right hy hz hsum =>
      let t : ModSeven := (z : ModSeven)
      have hy0 : (y : ModSeven) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hy
      have ht : t ≠ 0 := by simpa [t, ZMod.natCast_eq_zero_iff] using hz
      have hx : (x : ModSeven) = t := by simpa [t, hy0] using hlin
      refine .yCarrier t ht hy0 rfl hx ?_
      rw [← hfst]
      have h := congrArg (fun a : ℤ => (a : ModSeven))
        (cyclotomicSevenFst_sub_right_cube (z : ℤ) (y : ℤ))
      push_cast at h
      simp [hy0] at h
      dsimp [t]
      linear_combination h
  | left hz hy hsum =>
      let t : ModSeven := (y : ModSeven)
      have hz0 : (z : ModSeven) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hz
      have ht : t ≠ 0 := by simpa [t, ZMod.natCast_eq_zero_iff] using hy
      have hx : (x : ModSeven) = -t := by
        rw [hz0] at hlin
        simpa [t] using eq_neg_of_add_eq_zero_left hlin
      refine .zCarrier t ht rfl hz0 hx ?_
      rw [← hfst]
      have h := congrArg (fun a : ℤ => (a : ModSeven))
        (cyclotomicSevenFst_add_left_cube (z : ℤ) (y : ℤ))
      push_cast at h
      simp [hz0] at h
      dsimp [t]
      linear_combination h
  | sum hsum hy hz =>
      let t : ModSeven := (y : ModSeven)
      have hsum0 : (y : ModSeven) + (z : ModSeven) = 0 := by
        rw [← Nat.cast_add]
        exact (ZMod.natCast_eq_zero_iff _ _).2 hsum
      have ht : t ≠ 0 := by simpa [t, ZMod.natCast_eq_zero_iff] using hy
      have hzneg : (z : ModSeven) = -t := by
        dsimp [t]
        linear_combination hsum0
      have hx : (x : ModSeven) = -2 * t := by
        rw [hzneg] at hlin
        dsimp [t] at hlin ⊢
        linear_combination hlin
      refine .sumCarrier t ht rfl hzneg hx ?_
      rw [← hfst]
      have h := congrArg (fun a : ℤ => (a : ModSeven))
        (cyclotomicSevenFst_add_left_cube (z : ℤ) (y : ℤ))
      push_cast at h
      simp [hzneg] at h
      dsimp [t]
      linear_combination h

theorem AwayCoordinateNormalForm.rootLinear_ne_zero {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : awayRootLinearModSeven p ≠ 0 := by
  intro h
  apply p.root_norm_not_seven_dvd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  rw [traceOneNorm_mod_seven_eq_linear_sq]
  change ((p.root.fst : ModSeven) + 4 * (p.root.snd : ModSeven)) ^ 2 = 0 ^ 2
  exact congrArg (fun a : ModSeven => a ^ 2) h

end DkMath.FLT.Seven
