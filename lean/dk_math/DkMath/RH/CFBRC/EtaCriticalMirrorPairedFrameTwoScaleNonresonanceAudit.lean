/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/--
The canonical full-density block schedule `N(K)=2K`.  Its terminal-to-initial
pair-left endpoint ratio tends to three.
-/
def etaPairFullDensityBlockSchedule :
    EtaPairPositiveDensityBlockSchedule where
  blockLength := fun K : ℕ => 2 * K
  density := 1
  density_pos := by norm_num
  blockLength_tendsto_atTop := by
    apply StrictMono.tendsto_atTop
    intro K L hKL
    change 2 * K < 2 * L
    omega
  relativeLength_tendsto_density := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) 0 1 2 (d := 2) (by norm_num)
    simpa [etaPairFrameLeftEndpoint, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc,
      Nat.cast_add, Nat.cast_mul] using h

@[simp]
theorem etaPairFullDensityBlockSchedule_blockLength
    (K : ℕ) :
    etaPairFullDensityBlockSchedule.blockLength K = 2 * K :=
  rfl

@[simp]
theorem etaPairFullDensityBlockSchedule_density :
    etaPairFullDensityBlockSchedule.density = 1 :=
  rfl

namespace EtaPairPositiveDensityBlockSchedule

/-- For `N(K)=2K`, the limiting relative phase is `s.im * log 3`. -/
theorem etaPairFullDensityBlockSchedule_scheduledBlockPhase_tendsto
    (s : ℂ) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockPhase s)
      atTop
      (nhds (s.im * Real.log 3)) := by
  convert etaPairFullDensityBlockSchedule.scheduledBlockPhase_tendsto s using 1;
    norm_num [etaPairFullDensityBlockSchedule]

/-- For `N(K)=2K`, the relative rotation tends to `exp(I * s.im * log 3)`. -/
theorem etaPairFullDensityBlockSchedule_scheduledBlockRotation_tendsto
    (s : ℂ) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (Complex.exp
          (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))))) := by
  convert etaPairFullDensityBlockSchedule.scheduledBlockRotation_tendsto s using 1;
    norm_num [etaPairFullDensityBlockSchedule, scheduledBlockRotationLimit]

end EtaPairPositiveDensityBlockSchedule

/-- A positive power of two cannot equal a power of three. -/
private theorem two_pow_ne_three_pow_of_pos
    {m n : ℕ} (hm : 0 < m) :
    (2 : ℕ) ^ m ≠ 3 ^ n := by
  intro hpow
  have htwo_dvd : 2 ∣ (2 : ℕ) ^ m :=
    dvd_pow_self 2 hm.ne'
  rw [hpow] at htwo_dvd
  have htwo_dvd_three : 2 ∣ 3 :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_two htwo_dvd
  norm_num at htwo_dvd_three

/--
For a strictly positive frequency, the doubling and tripling rotations cannot
both be resonant.  Simultaneous resonance would force a positive power of two
to equal a positive power of three.
-/
private theorem positive_twoScaleRotation_nonresonant
    {t : ℝ} (ht : 0 < t) :
    ¬(
      Complex.exp
          (Complex.I * (((t * Real.log 2 : ℝ) : ℂ))) = 1 ∧
        Complex.exp
          (Complex.I * (((t * Real.log 3 : ℝ) : ℂ))) = 1) := by
  rintro ⟨h2, h3⟩
  rcases Complex.exp_eq_one_iff.mp h2 with ⟨a, ha⟩
  rcases Complex.exp_eq_one_iff.mp h3 with ⟨b, hb⟩
  have haReal :
      t * Real.log 2 = (a : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im ha
    norm_num [Complex.mul_im, mul_assoc] at h
    rw [Complex.log_re] at h
    norm_num at h
    exact h
  have hbReal :
      t * Real.log 3 = (b : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hb
    norm_num [Complex.mul_im, mul_assoc] at h
    rw [Complex.log_re] at h
    norm_num at h
    exact h
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have haCastPos : 0 < (a : ℝ) := by
    apply pos_of_mul_pos_right
    · nlinarith [haReal, htwoPi]
    · positivity
  have hbCastPos : 0 < (b : ℝ) := by
    apply pos_of_mul_pos_right
    · nlinarith [hbReal, htwoPi]
    · positivity
  have haPos : 0 < a := by exact_mod_cast haCastPos
  have hbPos : 0 < b := by exact_mod_cast hbCastPos
  let m : ℕ := b.toNat
  let n : ℕ := a.toNat
  have hbToNat : (m : ℤ) = b := by
    dsimp [m]
    exact Int.toNat_of_nonneg hbPos.le
  have haToNat : (n : ℤ) = a := by
    dsimp [n]
    exact Int.toNat_of_nonneg haPos.le
  have hm : 0 < m := by
    dsimp [m]
    have hcast := Int.toNat_of_nonneg hbPos.le
    by_contra hnot
    have hzero : b.toNat = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hcast
    omega
  have hcrossInt :
      (b : ℝ) * Real.log 2 =
        (a : ℝ) * Real.log 3 := by
    apply mul_left_cancel₀ ht.ne'
    calc
      t * ((b : ℝ) * Real.log 2) =
          (b : ℝ) * (t * Real.log 2) := by ring
      _ = (b : ℝ) * ((a : ℝ) * (2 * Real.pi)) := by
        rw [haReal]
      _ = (a : ℝ) * ((b : ℝ) * (2 * Real.pi)) := by ring
      _ = (a : ℝ) * (t * Real.log 3) := by
        rw [hbReal]
      _ = t * ((a : ℝ) * Real.log 3) := by ring
  have hbCast : (m : ℝ) = (b : ℝ) := by
    exact_mod_cast hbToNat
  have haCast : (n : ℝ) = (a : ℝ) := by
    exact_mod_cast haToNat
  have hcross :
      (m : ℝ) * Real.log 2 =
        (n : ℝ) * Real.log 3 := by
    rw [hbCast, haCast]
    exact hcrossInt
  have hpowReal :
      (2 : ℝ) ^ m = (3 : ℝ) ^ n := by
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℝ) :=
        (Real.rpow_natCast 2 m).symm
      _ = Real.exp (Real.log 2 * (m : ℝ)) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ = Real.exp (Real.log 3 * (n : ℝ)) := by
        congr 1
        simpa [mul_comm] using hcross
      _ = (3 : ℝ) ^ (n : ℝ) :=
        (Real.rpow_def_of_pos (by norm_num) _).symm
      _ = (3 : ℝ) ^ n :=
        Real.rpow_natCast 3 n
  have hpowNat : (2 : ℕ) ^ m = 3 ^ n := by
    exact_mod_cast hpowReal
  exact two_pow_ne_three_pow_of_pos hm hpowNat

/--
At every nonzero imaginary height, at least one of the doubling or tripling
relative-frame limits is nontrivial.
-/
theorem etaPairTwoScaleRotation_nonresonant
    {s : ℂ} (him : s.im ≠ 0) :
    Complex.exp
          (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))) ≠ 1 ∨
      Complex.exp
          (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))) ≠ 1 := by
  by_contra hboth
  push Not at hboth
  rcases lt_or_gt_of_ne him with hneg | hpos
  · apply positive_twoScaleRotation_nonresonant (neg_pos.mpr hneg)
    constructor
    · calc
        Complex.exp
            (Complex.I * (((-s.im * Real.log 2 : ℝ) : ℂ))) =
            Complex.exp
              (-(Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ)))) := by
                congr 1
                push_cast
                ring
        _ =
            (Complex.exp
              (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))))⁻¹ :=
          Complex.exp_neg _
        _ = 1 := by rw [hboth.1, inv_one]
    · calc
        Complex.exp
            (Complex.I * (((-s.im * Real.log 3 : ℝ) : ℂ))) =
            Complex.exp
              (-(Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ)))) := by
                congr 1
                push_cast
                ring
        _ =
            (Complex.exp
              (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))))⁻¹ :=
          Complex.exp_neg _
        _ = 1 := by rw [hboth.2, inv_one]
  · exact positive_twoScaleRotation_nonresonant hpos hboth

/-- The named half-density and full-density limit rotations cannot both be one. -/
theorem etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_ne_one
    {s : ℂ} (him : s.im ≠ 0) :
    etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1 ∨
      etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1 := by
  convert etaPairTwoScaleRotation_nonresonant him using 1 <;>
    norm_num [EtaPairPositiveDensityBlockSchedule.scheduledBlockRotationLimit,
      etaPairHalfDensityBlockSchedule, etaPairFullDensityBlockSchedule,
      Complex.ofReal_log]

/--
Certificate collecting the two explicit scale limits and their nonresonance.
This is a relative-frame invariant; it is not yet a zero/nonzero collision with
the zeta-zero condition.
-/
structure EtaPairTwoScaleNonresonanceCertificate
    (s : ℂ) : Prop where
  doubling_rotation_tendsto :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s))
  tripling_rotation_tendsto :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s))
  at_least_one_limit_ne_one :
    etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1 ∨
      etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1

/-- Every nonreal point carries the two-scale relative-frame certificate. -/
theorem etaPairTwoScaleNonresonanceCertificate_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    EtaPairTwoScaleNonresonanceCertificate s := by
  exact
    ⟨etaPairHalfDensityBlockSchedule.scheduledBlockRotation_tendsto s,
      etaPairFullDensityBlockSchedule.scheduledBlockRotation_tendsto s,
      etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_ne_one him⟩

end DkMath.RH.CFBRCProjection
