/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.ModSevenSectors

#print "file: DkMath.FLT.Seven.AwaySecondCoordinateLoad"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem traceOne_norm_pow (a : TraceOneInt (-2)) (n : ℕ) :
    norm (a ^ n) = norm a ^ n := by
  induction n with
  | zero => simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  | succ n ih => rw [pow_succ, traceOne_norm_mul, ih, pow_succ]

theorem AwayCoordinateNormalForm.root_norm_not_seven_dvd {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ¬ (7 : ℤ) ∣ norm p.root := by
  have hyz := (right_lt_of_fermat7Equation
    p.counterexample.hx p.counterexample.hEq).le
  have hGN7 : ¬ 7 ∣ DkMath.CosmicFormulaBinom.GN 7 (z - y) y := by
    intro h
    exact p.seven_not_dvd_gap
      ((seven_dvd_GN_seven_sub_iff z y hyz).mp h)
  have hnormEq :
      ((DkMath.CosmicFormulaBinom.GN 7 (z - y) y : ℕ) : ℤ) =
        norm p.root ^ 7 := by
    calc
      _ = norm (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)) :=
        GN_seven_sub_eq_traceOneNorm_negTwo z y hyz
      _ = norm (p.root ^ 7) := by rw [p.coordinate_eq]
      _ = _ := traceOne_norm_pow p.root 7
  intro hroot
  apply hGN7
  apply Int.ofNat_dvd.mp
  rw [hnormEq]
  exact dvd_pow hroot (by norm_num)

theorem AwayCoordinateNormalForm.sndCore_not_seven_dvd {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    ¬ (7 : ℤ) ∣ seventhPowerSndCore p.root.fst p.root.snd :=
  seven_not_dvd_seventhPowerSndCore_of_norm p.root_norm_not_seven_dvd

theorem cyclotomicSevenSnd_eq_neg_endpoint_product (z y : ℤ) :
    cyclotomicSevenSnd z y = -(y * z * (y + z)) := by
  simp [cyclotomicSevenSnd]
  ring

theorem away_endpoint_product_eq_natAbs_seventhPowerSnd {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) =
      Int.natAbs (seventhPowerSnd p.root.fst p.root.snd) := by
  have h := p.snd_eq
  rw [cyclotomicSevenSnd_eq_neg_endpoint_product] at h
  rw [← h, Int.natAbs_neg]
  exact_mod_cast (Int.natAbs_of_nonneg
    (show 0 ≤ (y : ℤ) * (z : ℤ) * ((y : ℤ) + (z : ℤ)) by positivity)).symm

theorem away_endpoint_product_load_eq {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) =
      7 * Int.natAbs p.root.snd *
        Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) := by
  rw [away_endpoint_product_eq_natAbs_seventhPowerSnd p,
    seventhPowerSnd_eq_seven_mul, Int.natAbs_mul, Int.natAbs_mul]
  norm_num

theorem AwayCoordinateNormalForm.sndCore_ne_zero {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    seventhPowerSndCore p.root.fst p.root.snd ≠ 0 := by
  intro h
  apply p.sndCore_not_seven_dvd
  rw [h]
  exact dvd_zero 7

theorem AwayCoordinateNormalForm.root_snd_ne_zero {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : p.root.snd ≠ 0 := by
  intro hv
  have hload := away_endpoint_product_load_eq p
  rw [hv] at hload
  norm_num at hload
  have hy : 0 < y := p.counterexample.hy
  have hz : 0 < z := p.counterexample.hz
  omega

theorem AwayCoordinateNormalForm.seven_not_dvd_natAbs_sndCore {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    ¬ 7 ∣ Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) := by
  intro h
  exact p.sndCore_not_seven_dvd (Int.natCast_dvd.mpr h)

theorem padicValNat_unique_factor_of_triple {a b c : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hb : ¬ 7 ∣ b) (hc : ¬ 7 ∣ c) :
    padicValNat 7 (a * b * c) = padicValNat 7 a := by
  rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0,
    padicValNat.mul ha0 hb0,
    padicValNat.eq_zero_of_not_dvd hb,
    padicValNat.eq_zero_of_not_dvd hc]
  omega

theorem padicValNat_seven_mul_of_core_not_dvd {v core : ℕ}
    (hv0 : v ≠ 0) (hc0 : core ≠ 0) (hc : ¬ 7 ∣ core) :
    padicValNat 7 (7 * v * core) = 1 + padicValNat 7 v := by
  rw [padicValNat.mul (mul_ne_zero (by norm_num) hv0) hc0,
    padicValNat.mul (by norm_num) hv0,
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd hc]
  omega

end DkMath.FLT.Seven
