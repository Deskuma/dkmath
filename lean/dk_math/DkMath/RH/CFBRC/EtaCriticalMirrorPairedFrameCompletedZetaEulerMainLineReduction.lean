/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerRemainderCollapse
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The normalized nearby `GammaR * zeta` carrier appearing in the Euler-main
mismatch.  On the zero locus this is exactly the canonical completed-zeta slope
carrier.
-/
noncomputable def etaCriticalMirrorNormalizedNearbyGammaZetaCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  (completedZetaCanonicalDisplacement k)⁻¹ *
    (Complex.Gammaℝ
        (s + completedZetaCanonicalDisplacement k) *
      riemannZeta
        (s + completedZetaCanonicalDisplacement k))

/-- On the zero locus, the nearby Gamma-zeta carrier is the canonical slope carrier. -/
theorem etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_eq_slopeCarrier_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s =
      completedZetaCanonicalSlopeCarrier k s := by
  rw [completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero hs]
  exact (normalizedNearbyCompletedZeta_eq_gammaR_mul_riemannZeta hs k).symm

/-- The nearby Gamma-zeta carrier already approaches the fixed slope line. -/
theorem etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s))
      atTop (nhds 0) := by
  have h := completedZetaCanonicalSlopeCarrier_tendsto_global_line hs
  refine h.congr' (Eventually.of_forall fun k => ?_)
  simp [etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_eq_slopeCarrier_of_zero hs]

/-- Transverse defect of the explicit dominant Euler half-endpoint main carrier. -/
noncomputable def etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
    (completedZetaCanonicalSlopeDirection s)
    (etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s)

/--
The Euler-main / nearby-value mismatch is exactly the Euler-main line defect
minus the already locked nearby slope-carrier defect.
-/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError_eq_main_sub_nearby
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError k s =
      etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError k s -
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s) := by
  unfold etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError
  unfold etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainMismatchCarrier
  unfold etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError
  unfold etaCriticalMirrorNormalizedNearbyGammaZetaCarrier
  simp [complexRealLineDefect, mul_sub]

/-- The direct Euler-main slope-line collapse. -/
def EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError k s)
      atTop (nhds 0)

/--
Because the nearby Gamma-zeta quotient is already line-locked, its mismatch
collapse is exactly direct line collapse of the Euler half-endpoint main
carrier.
-/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse_iff_mainCarrier :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse ↔
      EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse := by
  constructor
  · intro hmismatch s hs him
    have hm := hmismatch hs him
    have hn :=
      etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line hs
    have hsum := hm.add hn
    have hsum' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError k s +
              complexRealLineDefect
                (completedZetaCanonicalSlopeDirection s)
                (etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s))
          atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    refine hsum'.congr' (Eventually.of_forall fun k => ?_)
    rw [etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError_eq_main_sub_nearby]
    ring
  · intro hmain s hs him
    have hm := hmain hs him
    have hn :=
      etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line hs
    have hdiff := hm.sub hn
    have hdiff' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError k s -
              complexRealLineDefect
                (completedZetaCanonicalSlopeDirection s)
                (etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s))
          atTop (nhds 0) := by
      simpa only [sub_zero] using hdiff
    refine hdiff'.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError_eq_main_sub_nearby
        k s).symm

/-- RH now follows from line collapse of the explicit Euler main carrier alone. -/
theorem riemannHypothesis_of_weightedTailEulerMainCarrierTransverseCollapse
    (hmain : EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMainTransverseCollapse
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse_iff_mainCarrier.mpr
      hmain)

#print axioms etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_eq_slopeCarrier_of_zero
#print axioms etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse_iff_mainCarrier
#print axioms riemannHypothesis_of_weightedTailEulerMainCarrierTransverseCollapse

end DkMath.RH.CFBRCProjection
