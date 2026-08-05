/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionRoadmap
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology ComplexConjugate

/-- A unit-complex square equal to one is projectively trivial. -/
theorem etaPairProjectiveUnitRotation_of_mul_self_eq_one
    {z : ℂ} (hz : z * z = 1) :
    EtaPairProjectiveUnitRotation z := by
  have hfactor : (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z + 1) = z * z - 1 := by ring
      _ = 0 := by rw [hz]; norm_num
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · right
    have hshift := congrArg (fun w : ℂ => w - 1) hplus
    simpa using hshift

/-- Pair-left base rotations have unit conjugate product. -/
theorem etaPairBaseRotation_mul_conj_eq_one
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation s k * conj (etaPairBaseRotation s k) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    norm_etaPairBaseRotation]
  norm_num

/--
A noncollapsing carrier cancels no nonzero asymptotic coefficient.
This is the quantitative same-object step used by the line collision proof.
-/
theorem tendsto_one_of_mul_sub_one_tendsto_zero_of_eventually_norm_lower_bound
    {q z : ℕ → ℂ} {c : ℝ}
    (hc : 0 < c)
    (hproduct :
      Tendsto (fun k : ℕ => (q k - 1) * z k) atTop (nhds 0))
    (hlower : ∀ᶠ k : ℕ in atTop, c ≤ ‖z k‖) :
    Tendsto q atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormProduct :
      Tendsto
        (fun k : ℕ => ‖(q k - 1) * z k‖)
        atTop (nhds 0) := by
    change Tendsto
      ((fun w : ℂ => ‖w‖) ∘
        fun k : ℕ => (q k - 1) * z k)
      atTop (nhds 0)
    simpa only [norm_zero] using
      (continuous_norm.tendsto 0).comp hproduct
  have hupper :
      Tendsto
        (fun k : ℕ => ‖(q k - 1) * z k‖ / c)
        atTop (nhds 0) := by
    simpa using hnormProduct.div_const c
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => norm_nonneg (q k - 1)) ?_
  filter_upwards [hlower] with k hk
  apply (le_div_iff₀ hc).2
  calc
    ‖q k - 1‖ * c ≤ ‖q k - 1‖ * ‖z k‖ :=
      mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = ‖(q k - 1) * z k‖ := by rw [norm_mul]

/--
If one fixed projective phase normalizes every squared base rotation to one,
then every positive-density scheduled relative rotation has projectively
trivial limit.
-/
theorem scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
    (S : EtaPairPositiveDensityBlockSchedule)
    (s phase : ℂ)
    (hphase :
      Tendsto
        (fun k : ℕ =>
          phase * etaPairBaseRotation s k * etaPairBaseRotation s k)
        atTop (nhds 1)) :
    EtaPairProjectiveUnitRotation (S.scheduledBlockRotationLimit s) := by
  have hindex :
      Tendsto (fun K : ℕ => K + S.blockLength K) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro n
    exact eventually_atTop.2 ⟨n, by intro K hK; omega⟩
  have hterminal :
      Tendsto
        (fun K : ℕ =>
          phase *
            etaPairBaseRotation s (K + S.blockLength K) *
            etaPairBaseRotation s (K + S.blockLength K))
        atTop (nhds 1) :=
    hphase.comp hindex
  have hterminalProduct :
      Tendsto
        (fun K : ℕ =>
          (phase * etaPairBaseRotation s K * etaPairBaseRotation s K) *
            (S.scheduledBlockRotation s K *
              S.scheduledBlockRotation s K))
        atTop (nhds 1) := by
    refine hterminal.congr' (Eventually.of_forall fun K => ?_)
    simp only [EtaPairPositiveDensityBlockSchedule.scheduledBlockRotation,
      etaPairBaseRotation_add_eq_mul_blockRotation]
    ring
  have hrotationSq :
      Tendsto
        (fun K : ℕ =>
          S.scheduledBlockRotation s K * S.scheduledBlockRotation s K)
        atTop
        (nhds
          (S.scheduledBlockRotationLimit s *
            S.scheduledBlockRotationLimit s)) :=
    (S.scheduledBlockRotation_tendsto s).mul
      (S.scheduledBlockRotation_tendsto s)
  have hproductLimit :
      Tendsto
        (fun K : ℕ =>
          (phase * etaPairBaseRotation s K * etaPairBaseRotation s K) *
            (S.scheduledBlockRotation s K *
              S.scheduledBlockRotation s K))
        atTop
        (nhds
          (S.scheduledBlockRotationLimit s *
            S.scheduledBlockRotationLimit s)) := by
    simpa only [one_mul] using hphase.mul hrotationSq
  have hsq :
      S.scheduledBlockRotationLimit s *
          S.scheduledBlockRotationLimit s = 1 :=
    tendsto_nhds_unique hproductLimit hterminalProduct
  exact etaPairProjectiveUnitRotation_of_mul_self_eq_one hsq

/--
Conditional same-carrier collision theorem.

A nonzero carrier cannot asymptotically lie both on the rotating local line and
on one fixed global line when the doubling/tripling projective rotations are
nonresonant.  This is the main nonreal closure target of the new route.
-/
theorem etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
    {carrier : ℕ → ℂ → ℂ}
    (hlocal : EtaCriticalMirrorOffCriticalLocalMovingLineLock carrier)
    (hnoncollapse : EtaCriticalMirrorOffCriticalCarrierNoncollapse carrier)
    (hglobal : EtaCriticalMirrorGlobalZeroLineLock carrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  let direction : ℂ := hglobal.globalDirection s
  let phase : ℂ := direction * (conj direction)⁻¹
  have hdirection : direction ≠ 0 := by
    dsimp [direction]
    exact hglobal.globalDirection_ne_zero hs him
  have hlocalIm :
      Tendsto
        (fun k : ℕ =>
          (etaPairBaseRotation s k * carrier k s).im)
        atTop (nhds 0) := by
    simpa only [etaPairMovingRealLineDefect, complexRealAxisDefect] using
      hlocal hs him hre
  have hglobalIm :
      Tendsto
        (fun k : ℕ => (direction⁻¹ * carrier k s).im)
        atTop (nhds 0) := by
    simpa only [complexRealLineDefect, direction] using
      hglobal.carrier_tendsto_global_line hs him
  have hlocalTwice :
      Tendsto
        (fun k : ℕ =>
          2 * (etaPairBaseRotation s k * carrier k s).im)
        atTop (nhds 0) := by
    simpa using hlocalIm.const_mul 2
  have hlocalCast :
      Tendsto
        (fun k : ℕ =>
          ((2 * (etaPairBaseRotation s k * carrier k s).im : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hlocalTwice
    simpa [Function.comp_def] using h
  have hlocalSkew :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k * carrier k s -
            conj (etaPairBaseRotation s k * carrier k s))
        atTop (nhds 0) := by
    have h := hlocalCast.mul_const Complex.I
    refine h.congr' (Eventually.of_forall fun k => ?_)
    simpa using (Complex.sub_conj
      (etaPairBaseRotation s k * carrier k s)).symm
  have hlocalRotatedSkew :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k *
            (etaPairBaseRotation s k * carrier k s -
              conj (etaPairBaseRotation s k * carrier k s)))
        atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlocalSkew
    refine hnorm.congr' (Eventually.of_forall fun k => ?_)
    simp only [sub_zero, norm_mul, norm_etaPairBaseRotation, one_mul]
  have hlocalPhaseResidual :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k * etaPairBaseRotation s k * carrier k s -
            conj (carrier k s))
        atTop (nhds 0) := by
    refine hlocalRotatedSkew.congr' (Eventually.of_forall fun k => ?_)
    rw [map_mul]
    calc
      etaPairBaseRotation s k *
          (etaPairBaseRotation s k * carrier k s -
            conj (etaPairBaseRotation s k) * conj (carrier k s)) =
          etaPairBaseRotation s k * etaPairBaseRotation s k * carrier k s -
            (etaPairBaseRotation s k * conj (etaPairBaseRotation s k)) *
              conj (carrier k s) := by ring
      _ =
          etaPairBaseRotation s k * etaPairBaseRotation s k * carrier k s -
            conj (carrier k s) := by
        rw [etaPairBaseRotation_mul_conj_eq_one, one_mul]
  have hglobalTwice :
      Tendsto
        (fun k : ℕ => 2 * (direction⁻¹ * carrier k s).im)
        atTop (nhds 0) := by
    simpa using hglobalIm.const_mul 2
  have hglobalCast :
      Tendsto
        (fun k : ℕ =>
          ((2 * (direction⁻¹ * carrier k s).im : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hglobalTwice
    simpa [Function.comp_def] using h
  have hglobalSkew :
      Tendsto
        (fun k : ℕ =>
          direction⁻¹ * carrier k s -
            conj (direction⁻¹ * carrier k s))
        atTop (nhds 0) := by
    have h := hglobalCast.mul_const Complex.I
    refine h.congr' (Eventually.of_forall fun k => ?_)
    simpa using
      (Complex.sub_conj (direction⁻¹ * carrier k s)).symm
  have hglobalRotatedSkew :
      Tendsto
        (fun k : ℕ =>
          direction *
            (direction⁻¹ * carrier k s -
              conj (direction⁻¹ * carrier k s)))
        atTop (nhds 0) :=
    tendsto_const_nhds.mul hglobalSkew
  have hglobalPhaseResidual :
      Tendsto
        (fun k : ℕ =>
          carrier k s - phase * conj (carrier k s))
        atTop (nhds 0) := by
    refine hglobalRotatedSkew.congr' (Eventually.of_forall fun k => ?_)
    dsimp [phase]
    rw [map_mul, map_inv₀, mul_sub]
    rw [← mul_assoc direction direction⁻¹ (carrier k s),
      mul_inv_cancel₀ hdirection, one_mul]
    rw [← mul_assoc direction (conj direction)⁻¹ (conj (carrier k s))]
  have hphaseLocalResidual :
      Tendsto
        (fun k : ℕ =>
          phase *
            (etaPairBaseRotation s k * etaPairBaseRotation s k * carrier k s -
              conj (carrier k s)))
        atTop (nhds 0) :=
    tendsto_const_nhds.mul hlocalPhaseResidual
  have hcoefficientProduct :
      Tendsto
        (fun k : ℕ =>
          (phase * etaPairBaseRotation s k * etaPairBaseRotation s k - 1) *
            carrier k s)
        atTop (nhds 0) := by
    have hsum := hphaseLocalResidual.add hglobalPhaseResidual.neg
    refine hsum.congr' (Eventually.of_forall fun k => ?_)
    ring
  rcases hnoncollapse hs him hre with ⟨c, hc, hlower⟩
  have hphaseSquare :
      Tendsto
        (fun k : ℕ =>
          phase * etaPairBaseRotation s k * etaPairBaseRotation s k)
        atTop (nhds 1) :=
    tendsto_one_of_mul_sub_one_tendsto_zero_of_eventually_norm_lower_bound
      hc hcoefficientProduct hlower
  have hhalf :
      EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairHalfDensityBlockSchedule s phase hphaseSquare
  have hfull :
      EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairFullDensityBlockSchedule s phase hphaseSquare
  rcases
      etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
        him with hhalfNe | hfullNe
  · exact hhalfNe hhalf
  · exact hfullNe hfull


#print axioms etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core

end DkMath.RH.CFBRCProjection
