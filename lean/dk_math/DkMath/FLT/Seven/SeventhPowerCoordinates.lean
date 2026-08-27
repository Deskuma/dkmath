/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm

#print "file: DkMath.FLT.Seven.SeventhPowerCoordinates"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def seventhPowerFst (u v : ℤ) : ℤ :=
  u ^ 7 - 42 * u ^ 5 * v ^ 2 - 70 * u ^ 4 * v ^ 3
    + 70 * u ^ 3 * v ^ 4 + 126 * u ^ 2 * v ^ 5
    + 14 * u * v ^ 6 - 10 * v ^ 7

def seventhPowerSnd (u v : ℤ) : ℤ :=
  7 * u ^ 6 * v + 21 * u ^ 5 * v ^ 2 - 35 * u ^ 4 * v ^ 3
    - 105 * u ^ 3 * v ^ 4 - 21 * u ^ 2 * v ^ 5
    + 35 * u * v ^ 6 + 7 * v ^ 7

theorem traceOne_pow_seven_fst (u v : ℤ) :
    ((⟨u, v⟩ : TraceOneInt (-2)) ^ 7).fst = seventhPowerFst u v := by
  norm_num [pow_succ, seventhPowerFst,
    DkMath.NumberTheory.TraceOneQuadratic.mul]
  ring

theorem traceOne_pow_seven_snd (u v : ℤ) :
    ((⟨u, v⟩ : TraceOneInt (-2)) ^ 7).snd = seventhPowerSnd u v := by
  norm_num [pow_succ, seventhPowerSnd,
    DkMath.NumberTheory.TraceOneQuadratic.mul]
  ring

theorem traceOne_pow_seven_eq (u v : ℤ) :
    (⟨u, v⟩ : TraceOneInt (-2)) ^ 7 =
      ⟨seventhPowerFst u v, seventhPowerSnd u v⟩ := by
  apply traceOne_ext
  · exact traceOne_pow_seven_fst u v
  · exact traceOne_pow_seven_snd u v

def seventhPowerSndCore (u v : ℤ) : ℤ :=
  u ^ 6 + 3 * u ^ 5 * v - 5 * u ^ 4 * v ^ 2
    - 15 * u ^ 3 * v ^ 3 - 3 * u ^ 2 * v ^ 4
    + 5 * u * v ^ 5 + v ^ 6

theorem seventhPowerSnd_eq_seven_mul (u v : ℤ) :
    seventhPowerSnd u v = 7 * v * seventhPowerSndCore u v := by
  simp [seventhPowerSnd, seventhPowerSndCore]
  ring

theorem seventhPowerSndCore_mod_seven (u v : ℤ) :
    (seventhPowerSndCore u v : ZMod 7) =
      ((u : ZMod 7) ^ 2 + (u : ZMod 7) * (v : ZMod 7)
        + 2 * (v : ZMod 7) ^ 2) ^ 3 := by
  norm_num [seventhPowerSndCore]
  have h7 : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -(2 * (u : ZMod 7) ^ 4 * (v : ZMod 7) ^ 2
      + 4 * (u : ZMod 7) ^ 3 * (v : ZMod 7) ^ 3
      + 3 * (u : ZMod 7) ^ 2 * (v : ZMod 7) ^ 4
      + (u : ZMod 7) * (v : ZMod 7) ^ 5 + (v : ZMod 7) ^ 6) * h7

theorem seventhPowerFst_mod_seven (u v : ℤ) :
    (seventhPowerFst u v : ZMod 7) = (u : ZMod 7) + 4 * (v : ZMod 7) := by
  norm_num [seventhPowerFst]
  have h7 : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -(6 * (u : ZMod 7) ^ 5 * (v : ZMod 7) ^ 2
      + 10 * (u : ZMod 7) ^ 4 * (v : ZMod 7) ^ 3
      - 10 * (u : ZMod 7) ^ 3 * (v : ZMod 7) ^ 4
      - 18 * (u : ZMod 7) ^ 2 * (v : ZMod 7) ^ 5
      - 2 * (u : ZMod 7) * (v : ZMod 7) ^ 6
      + 2 * (v : ZMod 7)) * h7

theorem seventhPowerSnd_mod_seven (u v : ℤ) :
    (seventhPowerSnd u v : ZMod 7) = 0 := by
  rw [seventhPowerSnd_eq_seven_mul]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide]
  simp

theorem traceOneNorm_mod_seven_eq_linear_sq (u v : ℤ) :
    (norm (⟨u, v⟩ : TraceOneInt (-2)) : ZMod 7) =
      ((u : ZMod 7) + 4 * (v : ZMod 7)) ^ 2 := by
  simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  have h7 : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -((u : ZMod 7) * (v : ZMod 7) + 2 * (v : ZMod 7) ^ 2) * h7

theorem seven_not_dvd_seventhPowerSndCore_of_norm {u v : ℤ}
    (hnorm : ¬ (7 : ℤ) ∣ norm (⟨u, v⟩ : TraceOneInt (-2))) :
    ¬ (7 : ℤ) ∣ seventhPowerSndCore u v := by
  intro hcore
  have hcore0 : (seventhPowerSndCore u v : ZMod 7) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hcore
  rw [seventhPowerSndCore_mod_seven] at hcore0
  have hq :
      (u : ZMod 7) ^ 2 + (u : ZMod 7) * (v : ZMod 7) +
          2 * (v : ZMod 7) ^ 2 = 0 :=
    eq_zero_of_pow_eq_zero hcore0
  have hnorm0 : (norm (⟨u, v⟩ : TraceOneInt (-2)) : ZMod 7) = 0 := by
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    simpa using hq
  exact hnorm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hnorm0)

theorem fortyNine_dvd_seventhPowerSnd_iff {u v : ℤ}
    (hnorm : ¬ (7 : ℤ) ∣ norm (⟨u, v⟩ : TraceOneInt (-2))) :
    (49 : ℤ) ∣ seventhPowerSnd u v ↔ (7 : ℤ) ∣ v := by
  rw [seventhPowerSnd_eq_seven_mul]
  constructor
  · rintro ⟨k, hk⟩
    have h : (7 : ℤ) ∣ v * seventhPowerSndCore u v := by
      refine ⟨k, ?_⟩
      apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
      calc
        7 * (v * seventhPowerSndCore u v) =
            7 * v * seventhPowerSndCore u v := by ring
        _ = 49 * k := hk
        _ = 7 * (7 * k) := by ring
    rcases (Prime.dvd_mul (by norm_num : Prime (7 : ℤ))).mp h with hv | hc
    · exact hv
    · exact False.elim (seven_not_dvd_seventhPowerSndCore_of_norm hnorm hc)
  · rintro ⟨k, rfl⟩
    refine ⟨k * seventhPowerSndCore u (7 * k), ?_⟩
    ring

def ramifiedSeventhFst (u v : ℤ) : ℤ :=
  -u ^ 7 - 28 * u ^ 6 * v - 42 * u ^ 5 * v ^ 2
    + 210 * u ^ 4 * v ^ 3 + 350 * u ^ 3 * v ^ 4
    - 42 * u ^ 2 * v ^ 5 - 154 * u * v ^ 6 - 18 * v ^ 7

def ramifiedSeventhSnd (u v : ℤ) : ℤ :=
  2 * u ^ 7 + 7 * u ^ 6 * v - 63 * u ^ 5 * v ^ 2
    - 175 * u ^ 4 * v ^ 3 + 35 * u ^ 3 * v ^ 4
    + 231 * u ^ 2 * v ^ 5 + 63 * u * v ^ 6 - 13 * v ^ 7

theorem ramifiedSeventhFst_eq (u v : ℤ) :
    ramifiedSeventhFst u v = -seventhPowerFst u v - 4 * seventhPowerSnd u v := by
  simp [ramifiedSeventhFst, seventhPowerFst, seventhPowerSnd]
  ring

theorem ramifiedSeventhSnd_eq (u v : ℤ) :
    ramifiedSeventhSnd u v = 2 * seventhPowerFst u v + seventhPowerSnd u v := by
  simp [ramifiedSeventhSnd, seventhPowerFst, seventhPowerSnd]
  ring

theorem sevenAxis_mul_pow_seven_eq (u v : ℤ) :
    sevenAxis * (⟨u, v⟩ : TraceOneInt (-2)) ^ 7 =
      ⟨ramifiedSeventhFst u v, ramifiedSeventhSnd u v⟩ := by
  rw [traceOne_pow_seven_eq]
  apply traceOne_ext
  · simpa [ramifiedSeventhFst_eq] using
      sevenAxis_mul_fst (seventhPowerFst u v) (seventhPowerSnd u v)
  · simpa [ramifiedSeventhSnd_eq] using
      sevenAxis_mul_snd (seventhPowerFst u v) (seventhPowerSnd u v)

theorem ramifiedSeventhFst_mod_seven (u v : ℤ) :
    (ramifiedSeventhFst u v : ZMod 7) =
      -((u : ZMod 7) + 4 * (v : ZMod 7)) := by
  rw [ramifiedSeventhFst_eq]
  push_cast
  rw [seventhPowerFst_mod_seven, seventhPowerSnd_mod_seven]
  ring

theorem ramifiedSeventhSnd_mod_seven (u v : ℤ) :
    (ramifiedSeventhSnd u v : ZMod 7) =
      2 * ((u : ZMod 7) + 4 * (v : ZMod 7)) := by
  rw [ramifiedSeventhSnd_eq]
  push_cast
  rw [seventhPowerFst_mod_seven, seventhPowerSnd_mod_seven]
  ring

end DkMath.FLT.Seven
