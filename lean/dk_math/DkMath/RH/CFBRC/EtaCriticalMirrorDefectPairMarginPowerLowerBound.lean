/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityBlock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairMarginPowerLowerBound"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped BigOperators

private theorem etaPairFrameLeftEndpoint_le_rightEndpoint_powerLowerBound
    (k : ℕ) :
    etaPairFrameLeftEndpoint k ≤ etaPairFrameRightEndpoint k := by
  unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
  exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)

private theorem etaPairRadialDecay_continuousOn_pair_powerLowerBound
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaPairRadialDecay s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaPairRadialDecay
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_powerLowerBound k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorContinuousWeightR_continuousOn_pair_powerLowerBound
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaCriticalMirrorContinuousWeightR s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaCriticalMirrorContinuousWeightR
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_powerLowerBound k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorRightPairMarginIntegrand_intervalIntegrable_powerLowerBound
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
          etaCriticalMirrorContinuousWeightR s x)
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    ((continuousOn_const.mul
      (etaPairRadialDecay_continuousOn_pair_powerLowerBound s k)).mul
        (etaCriticalMirrorContinuousWeightR_continuousOn_pair_powerLowerBound
          s k)).intervalIntegrable

private theorem etaCriticalMirrorLeftPairMarginIntegrand_intervalIntegrable_powerLowerBound
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        (s.im ^ 2 / 4) * etaPairRadialDecay s x)
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    (continuousOn_const.mul
      (etaPairRadialDecay_continuousOn_pair_powerLowerBound s k)).intervalIntegrable

/-- The growing-side radial and transport factors combine to one real power. -/
theorem etaPairRadialDecay_mul_continuousWeightR_eq_rpow
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaPairRadialDecay s x *
        etaCriticalMirrorContinuousWeightR s x =
      x ^ (s.re - 2) := by
  unfold etaPairRadialDecay etaCriticalMirrorContinuousWeightR centeredSigma
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- Explicit right-endpoint lower bound for one growing-side pair margin. -/
noncomputable def etaCriticalMirrorRightPairMarginPowerLowerBound
    (s : ℂ) (k : ℕ) : ℝ :=
  (s.im ^ 2 / 4) *
    etaPairFrameRightEndpoint k ^ (s.re - 2)

/-- Explicit right-endpoint lower bound for one decaying-side pair margin. -/
noncomputable def etaCriticalMirrorLeftPairMarginPowerLowerBound
    (s : ℂ) (k : ℕ) : ℝ :=
  (s.im ^ 2 / 4) *
    etaPairFrameRightEndpoint k ^ (-s.re - 1)

/--
If the growing-side exponent is nonpositive, the right endpoint gives a lower
bound for the complete right pair-margin integral.
-/
theorem etaCriticalMirrorRightPairMarginPowerLowerBound_le
    (s : ℂ) (k : ℕ) (hre : s.re ≤ 2) :
    etaCriticalMirrorRightPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorRightPairMargin s k := by
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_powerLowerBound k
  unfold etaCriticalMirrorRightPairMarginPowerLowerBound
  unfold etaCriticalMirrorRightPairMargin
  calc
    (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint k ^ (s.re - 2) =
      ∫ _x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        (s.im ^ 2 / 4) *
          etaPairFrameRightEndpoint k ^ (s.re - 2) := by
      rw [intervalIntegral.integral_const]
      simp [etaPairFrameLeftEndpoint, etaPairFrameRightEndpoint]
    _ ≤
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
          etaCriticalMirrorContinuousWeightR s x := by
      apply intervalIntegral.integral_mono_on
        hle intervalIntegrable_const
        (etaCriticalMirrorRightPairMarginIntegrand_intervalIntegrable_powerLowerBound
          s k)
      intro x hx
      have hxpos : 0 < x :=
        (etaPairFrameLeftEndpoint_pos k).trans_le hx.1
      have hpow :
          etaPairFrameRightEndpoint k ^ (s.re - 2) ≤
            x ^ (s.re - 2) :=
        Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by linarith)
          hxpos (etaPairFrameRightEndpoint_pos k) hx.2
      rw [etaPairRadialDecay_mul_continuousWeightR_eq_rpow s hxpos]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/--
If the decaying-side exponent is nonpositive, the right endpoint gives a lower
bound for the complete left pair-margin integral.
-/
theorem etaCriticalMirrorLeftPairMarginPowerLowerBound_le
    (s : ℂ) (k : ℕ) (hre : -1 ≤ s.re) :
    etaCriticalMirrorLeftPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorLeftPairMargin s k := by
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_powerLowerBound k
  unfold etaCriticalMirrorLeftPairMarginPowerLowerBound
  unfold etaCriticalMirrorLeftPairMargin
  calc
    (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint k ^ (-s.re - 1) =
      ∫ _x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        (s.im ^ 2 / 4) *
          etaPairFrameRightEndpoint k ^ (-s.re - 1) := by
      rw [intervalIntegral.integral_const]
      simp [etaPairFrameLeftEndpoint, etaPairFrameRightEndpoint]
    _ ≤
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        (s.im ^ 2 / 4) * etaPairRadialDecay s x := by
      apply intervalIntegral.integral_mono_on
        hle intervalIntegrable_const
        (etaCriticalMirrorLeftPairMarginIntegrand_intervalIntegrable_powerLowerBound
          s k)
      intro x hx
      have hxpos : 0 < x :=
        (etaPairFrameLeftEndpoint_pos k).trans_le hx.1
      have hpow :
          etaPairFrameRightEndpoint k ^ (-s.re - 1) ≤
            x ^ (-s.re - 1) :=
        Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by linarith)
          hxpos (etaPairFrameRightEndpoint_pos k) hx.2
      unfold etaPairRadialDecay
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A nontrivial zero automatically satisfies the right pair power lower bound. -/
theorem etaCriticalMirrorRightPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorRightPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorRightPairMargin s k := by
  have hm : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hre : s.re ≤ 2 := by
    simp [criticalMirror] at hm
    linarith
  exact etaCriticalMirrorRightPairMarginPowerLowerBound_le s k hre

/-- A nontrivial zero automatically satisfies the left pair power lower bound. -/
theorem etaCriticalMirrorLeftPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorLeftPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorLeftPairMargin s k := by
  have hre : 0 < s.re := nontrivialRiemannZetaZero_re_pos hs
  exact
    etaCriticalMirrorLeftPairMarginPowerLowerBound_le s k (by linarith)

/-- Endpoint-power lower bound for one complete growing-side finite block. -/
noncomputable def etaCriticalMirrorRightBlockMarginPowerLowerBound
    (s : ℂ) (K N : ℕ) : ℝ :=
  (N : ℝ) *
    ((s.im ^ 2 / 4) *
      etaPairFrameRightEndpoint (K + N) ^ (s.re - 2))

/-- Endpoint-power lower bound for one complete decaying-side finite block. -/
noncomputable def etaCriticalMirrorLeftBlockMarginPowerLowerBound
    (s : ℂ) (K N : ℕ) : ℝ :=
  (N : ℝ) *
    ((s.im ^ 2 / 4) *
      etaPairFrameRightEndpoint (K + N) ^ (-s.re - 1))

/-- The right block-margin sum dominates its explicit terminal-endpoint power. -/
theorem etaCriticalMirrorRightBlockMarginPowerLowerBound_le
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorRightBlockMarginPowerLowerBound s K N ≤
      etaCriticalMirrorRightBlockMarginSum s K N := by
  have hm : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hexp : s.re - 2 ≤ 0 := by
    simp [criticalMirror] at hm
    linarith
  unfold etaCriticalMirrorRightBlockMarginPowerLowerBound
  unfold etaCriticalMirrorRightBlockMarginSum
  rw [show
      (N : ℝ) *
          ((s.im ^ 2 / 4) *
            etaPairFrameRightEndpoint (K + N) ^ (s.re - 2)) =
        (Finset.range N).sum
          (fun _j : ℕ =>
            (s.im ^ 2 / 4) *
              etaPairFrameRightEndpoint (K + N) ^ (s.re - 2)) by
    simp]
  apply Finset.sum_le_sum
  intro j hj
  have hjlt : j < N := Finset.mem_range.mp hj
  have hendpoint :
      etaPairFrameRightEndpoint (K + j) ≤
        etaPairFrameRightEndpoint (K + N) := by
    unfold etaPairFrameRightEndpoint
    exact_mod_cast (by omega : 2 * (K + j) + 2 ≤ 2 * (K + N) + 2)
  have hpow :
      etaPairFrameRightEndpoint (K + N) ^ (s.re - 2) ≤
        etaPairFrameRightEndpoint (K + j) ^ (s.re - 2) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      hexp
      (etaPairFrameRightEndpoint_pos (K + j))
      (etaPairFrameRightEndpoint_pos (K + N))
      hendpoint
  calc
    (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint (K + N) ^ (s.re - 2) ≤
      (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint (K + j) ^ (s.re - 2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = etaCriticalMirrorRightPairMarginPowerLowerBound s (K + j) := rfl
    _ ≤ etaCriticalMirrorRightPairMargin s (K + j) :=
      etaCriticalMirrorRightPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
        hs (K + j)

/-- The left block-margin sum dominates its explicit terminal-endpoint power. -/
theorem etaCriticalMirrorLeftBlockMarginPowerLowerBound_le
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorLeftBlockMarginPowerLowerBound s K N ≤
      etaCriticalMirrorLeftBlockMarginSum s K N := by
  have hsre : 0 < s.re := nontrivialRiemannZetaZero_re_pos hs
  have hexp : -s.re - 1 ≤ 0 := by linarith
  unfold etaCriticalMirrorLeftBlockMarginPowerLowerBound
  unfold etaCriticalMirrorLeftBlockMarginSum
  rw [show
      (N : ℝ) *
          ((s.im ^ 2 / 4) *
            etaPairFrameRightEndpoint (K + N) ^ (-s.re - 1)) =
        (Finset.range N).sum
          (fun _j : ℕ =>
            (s.im ^ 2 / 4) *
              etaPairFrameRightEndpoint (K + N) ^ (-s.re - 1)) by
    simp]
  apply Finset.sum_le_sum
  intro j hj
  have hjlt : j < N := Finset.mem_range.mp hj
  have hendpoint :
      etaPairFrameRightEndpoint (K + j) ≤
        etaPairFrameRightEndpoint (K + N) := by
    unfold etaPairFrameRightEndpoint
    exact_mod_cast (by omega : 2 * (K + j) + 2 ≤ 2 * (K + N) + 2)
  have hpow :
      etaPairFrameRightEndpoint (K + N) ^ (-s.re - 1) ≤
        etaPairFrameRightEndpoint (K + j) ^ (-s.re - 1) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      hexp
      (etaPairFrameRightEndpoint_pos (K + j))
      (etaPairFrameRightEndpoint_pos (K + N))
      hendpoint
  calc
    (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint (K + N) ^ (-s.re - 1) ≤
      (s.im ^ 2 / 4) *
        etaPairFrameRightEndpoint (K + j) ^ (-s.re - 1) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = etaCriticalMirrorLeftPairMarginPowerLowerBound s (K + j) := rfl
    _ ≤ etaCriticalMirrorLeftPairMargin s (K + j) :=
      etaCriticalMirrorLeftPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
        hs (K + j)

end DkMath.RH.CFBRCProjection
