/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameVariation
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGaugeAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Exact inverse gauge of the pair-left base rotation. -/
noncomputable def etaPairBaseCounterRotation
    (s : ℂ) (k : ℕ) : ℂ :=
  (etaPairBaseRotation s k)⁻¹

/-- The pair-left base rotation is never zero. -/
theorem etaPairBaseRotation_ne_zero
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation s k ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_etaPairBaseRotation]
  norm_num

/-- The inverse gauge also has unit norm. -/
theorem norm_etaPairBaseCounterRotation
    (s : ℂ) (k : ℕ) :
    ‖etaPairBaseCounterRotation s k‖ = 1 := by
  rw [etaPairBaseCounterRotation, norm_inv,
    norm_etaPairBaseRotation, inv_one]

/-- The inverse gauge cancels the pair-left base rotation exactly. -/
theorem etaPairBaseCounterRotation_mul_baseRotation
    (s : ℂ) (k : ℕ) :
    etaPairBaseCounterRotation s k * etaPairBaseRotation s k = 1 := by
  unfold etaPairBaseCounterRotation
  exact inv_mul_cancel₀ (etaPairBaseRotation_ne_zero s k)

/-- The cancellation also holds in the opposite multiplication order. -/
theorem etaPairBaseRotation_mul_counterRotation
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation s k * etaPairBaseCounterRotation s k = 1 := by
  unfold etaPairBaseCounterRotation
  exact mul_inv_cancel₀ (etaPairBaseRotation_ne_zero s k)

/--
One moving-frame defect pair after exact logarithmic gauge removal.

This definition deliberately tests whether cancelling the known pair-frame
rotation creates a new fixed-frame object.
-/
noncomputable def etaCriticalMirrorGaugeRenormalizedDefectPairTerm
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseCounterRotation s k *
    etaCriticalMirrorRotatedDefectPairTerm s k

/--
Exact gauge removal returns the original unrotated defect pair.  Hence this
renormalization introduces no new phase-separation information.
-/
theorem etaCriticalMirrorGaugeRenormalizedDefectPairTerm_eq
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorGaugeRenormalizedDefectPairTerm s k =
      etaCriticalMirrorDefectPairTerm s k := by
  unfold etaCriticalMirrorGaugeRenormalizedDefectPairTerm
  unfold etaCriticalMirrorRotatedDefectPairTerm
  rw [← mul_assoc,
    etaPairBaseCounterRotation_mul_baseRotation,
    one_mul]

/-- Finite partial sum of the exactly gauge-renormalized defect pairs. -/
noncomputable def etaCriticalMirrorGaugeRenormalizedDefectPairedPartial
    (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum
    (etaCriticalMirrorGaugeRenormalizedDefectPairTerm s)

/-- The gauge-renormalized partial is exactly the original defect paired partial. -/
theorem etaCriticalMirrorGaugeRenormalizedDefectPairedPartial_eq
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorGaugeRenormalizedDefectPairedPartial K s =
      etaCriticalMirrorDefectPairedPartial K s := by
  unfold etaCriticalMirrorGaugeRenormalizedDefectPairedPartial
  unfold etaCriticalMirrorDefectPairedPartial
  apply Finset.sum_congr rfl
  intro k hk
  exact etaCriticalMirrorGaugeRenormalizedDefectPairTerm_eq s k

/-- Fixed real projection of the gauge-renormalized finite partial. -/
noncomputable def etaCriticalMirrorGaugeRenormalizedProjectedPartial
    (K : ℕ) (ω s : ℂ) : ℝ :=
  (ω * etaCriticalMirrorGaugeRenormalizedDefectPairedPartial K s).re

/-- Every fixed projection after exact gauge removal is the original fixed projection. -/
theorem etaCriticalMirrorGaugeRenormalizedProjectedPartial_eq
    (K : ℕ) (ω s : ℂ) :
    etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s =
      etaCriticalMirrorProjectedDefectPairedPartial K ω s := by
  unfold etaCriticalMirrorGaugeRenormalizedProjectedPartial
  unfold etaCriticalMirrorProjectedDefectPairedPartial
  rw [etaCriticalMirrorGaugeRenormalizedDefectPairedPartial_eq]

/--
At a nonreal nontrivial zero, every fixed projection of the exactly
renormalized partial still tends to zero.  Cancelling the logarithmic frame
motion is therefore a pure gauge operation, not a common-half-plane provider.
-/
theorem etaCriticalMirrorGaugeRenormalizedProjectedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s)
      atTop (nhds 0) := by
  simpa only [etaCriticalMirrorGaugeRenormalizedProjectedPartial_eq] using
    etaCriticalMirrorProjectedDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
      (s := s) (ω := ω) hs him

end DkMath.RH.CFBRCProjection
