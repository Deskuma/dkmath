/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingRealLine
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionContracts"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- A rotation is projectively trivial when it is either `1` or `-1`. -/
def EtaPairProjectiveUnitRotation (z : ℂ) : Prop :=
  z = 1 ∨ z = -1

/--
Projective two-scale nonresonance.

Because a real line identifies opposite directions, ordinary nonresonance is
strengthened from `≠ 1` to `≠ ±1`. Simultaneous projective resonance at
height `s.im` would square to simultaneous ordinary resonance at height
`2 * s.im`, contradicting the existing doubling / tripling theorem.
-/
theorem etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
    {s : ℂ} (him : s.im ≠ 0) :
    ¬ EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) ∨
      ¬ EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s) := by
  by_contra hboth
  push Not at hboth
  norm_num
    [EtaPairPositiveDensityBlockSchedule.scheduledBlockRotationLimit,
      etaPairHalfDensityBlockSchedule, etaPairFullDensityBlockSchedule]
    at hboth
  have hprojectiveSquare :
      ∀ z : ℂ, EtaPairProjectiveUnitRotation z → z * z = 1 := by
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      norm_num
    · rw [hz]
      norm_num
  let s2 : ℂ := ⟨s.re, 2 * s.im⟩
  have hs2im : s2.im ≠ 0 := by
    dsimp [s2]
    exact mul_ne_zero (by norm_num) him
  have h2 :
      Complex.exp
          (Complex.I * (((s2.im * Real.log 2 : ℝ) : ℂ))) = 1 := by
    calc
      Complex.exp
          (Complex.I * (((s2.im * Real.log 2 : ℝ) : ℂ))) =
          Complex.exp
            ((Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))) +
              (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ)))) := by
                congr 1
                dsimp [s2]
                push_cast
                ring
      _ =
          Complex.exp
              (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))) *
            Complex.exp
              (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))) := by
                rw [Complex.exp_add]
      _ = 1 := by
        simpa [Complex.ofReal_log] using
          hprojectiveSquare
            (Complex.exp (Complex.I * (↑s.im * Complex.log 2))) hboth.1
  have h3 :
      Complex.exp
          (Complex.I * (((s2.im * Real.log 3 : ℝ) : ℂ))) = 1 := by
    calc
      Complex.exp
          (Complex.I * (((s2.im * Real.log 3 : ℝ) : ℂ))) =
          Complex.exp
            ((Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))) +
              (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ)))) := by
                congr 1
                dsimp [s2]
                push_cast
                ring
      _ =
          Complex.exp
              (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))) *
            Complex.exp
              (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))) := by
                rw [Complex.exp_add]
      _ = 1 := by
        simpa [Complex.ofReal_log] using
          hprojectiveSquare
            (Complex.exp (Complex.I * (↑s.im * Complex.log 3))) hboth.2
  rcases etaPairTwoScaleRotation_nonresonant (s := s2) hs2im with h2ne | h3ne
  · exact h2ne h2
  · exact h3ne h3

/-- Certificate for the projective two-scale nonresonance stage. -/
structure EtaPairProjectiveTwoScaleNonresonanceCertificate
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
  at_least_one_limit_not_projectively_trivial :
    ¬ EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) ∨
      ¬ EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s)

/-- Build the projective two-scale certificate at every nonreal point. -/
theorem etaPairProjectiveTwoScaleNonresonanceCertificate_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    EtaPairProjectiveTwoScaleNonresonanceCertificate s :=
  { doubling_rotation_tendsto :=
      etaPairHalfDensityBlockSchedule.scheduledBlockRotation_tendsto s
    tripling_rotation_tendsto :=
      etaPairFullDensityBlockSchedule.scheduledBlockRotation_tendsto s
    at_least_one_limit_not_projectively_trivial :=
      etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
        him }

/-- Signed transverse defect from a real line with complex direction `direction`. -/
noncomputable def complexRealLineDefect
    (direction z : ℂ) : ℝ :=
  (direction⁻¹ * z).im

/--
The side-aware normalized endpoint carrier used by the moving-line route.
It is defined from the existing endpoint itself, not from a desired global
line and not from the critical-line conclusion.
-/
noncomputable def etaCriticalMirrorDominantNormalizedEndpointCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  if s.re ≤ (1 : ℝ) / 2 then
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint s.re s k
  else
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
      (criticalMirror s).re s k

/-- Off-critical endpoint carriers approach their local pair-left moving real line. -/
def EtaCriticalMirrorOffCriticalLocalMovingLineLock
    (carrier : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    s.re ≠ (1 : ℝ) / 2 →
    Tendsto
      (fun k : ℕ =>
        etaPairMovingRealLineDefect s k (carrier k s))
      atTop (nhds 0)

/-- Off-critical endpoint carriers retain a positive asymptotic norm. -/
def EtaCriticalMirrorOffCriticalCarrierNoncollapse
    (carrier : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    s.re ≠ (1 : ℝ) / 2 →
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ k : ℕ in atTop, c ≤ ‖carrier k s‖

/-- Abstract external fixed global-line provider. -/
structure EtaCriticalMirrorGlobalZeroLineLock
    (carrier : ℕ → ℂ → ℂ) where
  globalDirection : ℂ → ℂ
  globalDirection_ne_zero :
    ∀ {s : ℂ},
      NontrivialRiemannZetaZero s →
      s.im ≠ 0 →
      globalDirection s ≠ 0
  carrier_tendsto_global_line :
    ∀ {s : ℂ},
      NontrivialRiemannZetaZero s →
      s.im ≠ 0 →
      Tendsto
        (fun k : ℕ =>
          complexRealLineDefect (globalDirection s) (carrier k s))
        atTop (nhds 0)

/-- The concrete dominant endpoint carrier approaches its local moving line. -/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock :
    EtaCriticalMirrorOffCriticalLocalMovingLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier := by
  intro s hs him hre
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have hrotated :=
      (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hleft).rotated_endpoint_tendsto
    have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
    have himaginary :
        Tendsto
          (fun k : ℕ =>
            (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
              s.re s k).im)
          atTop (nhds 0) := by
      have h :=
        (Complex.continuous_im.tendsto
          (-(-etaPairIndexNormalizedTailConstant s))).comp hrotated
      have hzero : (-(-etaPairIndexNormalizedTailConstant s)).im = 0 := by
        simp [etaPairIndexNormalizedTailConstant]
      simpa only [Function.comp_def, hzero, criticalMirror] using h
    simpa only [etaPairMovingRealLineDefect,
      complexRealAxisDefect,
      etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint,
      ite_eq_left hle, Function.comp_apply] using himaginary
  · have hrotated :=
      (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hright).rotated_endpoint_tendsto
    have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
    have himaginary :
        Tendsto
          (fun k : ℕ =>
            (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
              (1 - s.re) s k).im)
          atTop (nhds 0) := by
      have h :=
        (Complex.continuous_im.tendsto
          (-etaPairIndexNormalizedTailConstant (criticalMirror s))).comp
            hrotated
      have hzero :
          (-etaPairIndexNormalizedTailConstant
            ({ re := 1 - s.re, im := s.im } : ℂ)).im = 0 := by
        simp [etaPairIndexNormalizedTailConstant]
      simpa only [Function.comp_def, hzero, criticalMirror] using h
    simpa only [etaPairMovingRealLineDefect,
      complexRealAxisDefect,
      etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint,
      ite_eq_right hnotle, Function.comp_apply, criticalMirror] using himaginary

/-- The concrete dominant endpoint carrier does not collapse off critical. -/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse :
    EtaCriticalMirrorOffCriticalCarrierNoncollapse
      etaCriticalMirrorDominantNormalizedEndpointCarrier := by
  intro s hs him hre
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have cert :=
      etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hleft
    have hlimitPos :
        0 < ‖-etaPairIndexNormalizedTailConstant s‖ := by
      exact lt_of_le_of_ne
        (norm_nonneg _)
        (Ne.symm cert.norm_limit_ne_zero)
    refine ⟨‖-etaPairIndexNormalizedTailConstant s‖ / 2, by linarith, ?_⟩
    have heventually :
        ∀ᶠ k : ℕ in atTop,
          ‖-etaPairIndexNormalizedTailConstant s‖ / 2 <
            ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint s.re s k‖ := by
      exact cert.endpoint_norm_tendsto.eventually
        (Ioi_mem_nhds (by linarith))
    filter_upwards [heventually] with k hk
    have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
    simpa only [etaCriticalMirrorDominantNormalizedEndpointCarrier,
      ite_eq_left hle] using le_of_lt hk
  · have cert :=
      etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hright
    have hlimitPos :
        0 < ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ := by
      exact lt_of_le_of_ne
        (norm_nonneg _)
        (Ne.symm cert.norm_limit_ne_zero)
    refine
      ⟨‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ / 2,
        by linarith, ?_⟩
    have heventually :
        ∀ᶠ k : ℕ in atTop,
          ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ / 2 <
            ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
              (criticalMirror s).re s k‖ := by
      exact cert.endpoint_norm_tendsto.eventually
        (Ioi_mem_nhds (by linarith))
    filter_upwards [heventually] with k hk
    have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
    simpa only [etaCriticalMirrorDominantNormalizedEndpointCarrier,
      ite_eq_right hnotle] using le_of_lt hk

/-- Contract for the historical real-axis branch. -/
def StandardZetaRealAxisClosure : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im = 0 →
    s.re = (1 : ℝ) / 2

#print axioms etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock
#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse

end DkMath.RH.CFBRCProjection
