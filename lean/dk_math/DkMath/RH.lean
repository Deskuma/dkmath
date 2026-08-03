/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.RH.Basic
import DkMath.RH.Defs
import DkMath.RH.Lemmas
import DkMath.RH.Theorems
import DkMath.RH.EulerZeta
import DkMath.RH.EulerZetaLemmas
import DkMath.RH.HopcInfiniteLift
import DkMath.RH.CFBRCBridge
import DkMath.RH.CFBRC.OffCriticalExclusion
import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import DkMath.RH.CFBRC.MirrorThreatModel
import DkMath.RH.CFBRC.MirrorRootOfUnity
import DkMath.RH.CFBRC.MirrorAngleBranch
import DkMath.RH.CFBRC.MirrorIndexedRoot
import DkMath.RH.CFBRC.FiniteClosure
import DkMath.RH.CFBRC.FiniteClosurePermutation
import DkMath.RH.CFBRC.FiniteMassNormalization
import DkMath.RH.CFBRC.FiniteCenteredBridge
import DkMath.RH.CFBRC.EtaFiniteClosure
import DkMath.RH.CFBRC.StandardZetaBridge
import DkMath.RH.CFBRC.EtaEnergyBridge
import DkMath.RH.CFBRC.EtaEnergyNormalization
import DkMath.RH.CFBRC.EtaProjectedEnergyBridge
import DkMath.RH.CFBRC.EtaUnitRotationBridge
import DkMath.RH.CFBRC.EtaUnitRotationLimits
import DkMath.RH.CFBRC.EtaKUSState
import DkMath.RH.CFBRC.EtaKUSLimit
import DkMath.RH.CFBRC.EtaKUSProjectedCenterDecoder
import DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder
import DkMath.RH.CFBRC.EtaMirrorUnitSplit
import DkMath.RH.CFBRC.EtaKUSMirrorUnitBridge
import DkMath.RH.CFBRC.EtaKUSMirrorGapBridgeAudit
import DkMath.RH.CFBRC.EtaMirrorEndpointPairEnergy
import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization
import DkMath.RH.CFBRC.EtaMirrorEndpointDefinedShares
import DkMath.RH.CFBRC.EtaMirrorEndpointRegularizedLimits
import DkMath.RH.CFBRC.EtaMirrorEndpointNormalizationState
import DkMath.RH.CFBRC.EtaKUSMirrorAmplitudeBridge
import DkMath.RH.CFBRC.EtaKUSDecoderAgreementAudit
import DkMath.RH.CFBRC.ZeroLocusFactorBridge
import DkMath.RH.CFBRC.CompletedZetaBridge
import DkMath.RH.CFBRC.CriticalMirrorGeometry
import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits
import DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse
import DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport
import DkMath.RH.CFBRC.EtaCriticalMirrorWeightPressure
import DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedPhaseProjection
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization
import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightPressure
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientMargin
import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightThreshold
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit
import DkMath.RH.CFBRC.EtaEndpointIncrementDecoder
import DkMath.RH.Weave.Control.IndexShiftAudit
import DkMath.RH.Weave.Finite.PairEnergy
import DkMath.RH.Weave.Finite.EtaPairDecomposition
import DkMath.RH.Weave.Analytic.EtaLimitBridge
import DkMath.RH.Weave.Analytic.EtaEvenPairing
import DkMath.RH.Weave.Analytic.EtaPairedLimit
import DkMath.RH.Weave.Analytic.EtaTermDecay
import DkMath.RH.Weave.Analytic.EtaPairDerivative
import DkMath.RH.Weave.Analytic.EtaPairIntegral
import DkMath.RH.Weave.Analytic.EtaPairPhaseSpan
import DkMath.RH.Weave.Analytic.EtaAbsoluteConvergence
import DkMath.RH.Weave.Analytic.EtaFiniteFactorization
import DkMath.RH.Weave.Analytic.EtaZetaIdentification
import DkMath.RH.Weave.Analytic.EtaHalfPlaneReconstruction
import DkMath.RH.Weave.Analytic.EtaPairedSummability
import DkMath.RH.Weave.Analytic.EtaPairedIdentification
import DkMath.RH.Weave.Analytic.EtaPairedHolomorphic
import DkMath.RH.Weave.Analytic.EtaPoleAudit
import DkMath.RH.Weave.Analytic.EtaContinuationDomains
import DkMath.RH.Weave.Analytic.EtaPairedContinuation
import DkMath.RH.Weave.Analytic.EtaEnergyLimit
import DkMath.RH.EulerZetaConvergence

#print "file: DkMath.RH"

-- ============================================================================

namespace DkMath.RH

open DkMath.Basic
open DkMath.RH.Basic

#eval printValue ident
#eval printValue name

open CFBRCProjection

-- cid: 6a6deaaf-6240-83e8-8f97-f1ef176868b2
theorem standardZeta_map_zero_iff_riemannHypothesis
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ) :
    (∀ {s : ℂ}, NontrivialRiemannZetaZero s →
      offCriticalCFBRC d s.re (phase s) = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_standardZeta_map_zero hd phase h
  · intro hRH s hs
    apply
      (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re (phase s)).2
    exact
      (riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH)
        s hs

end DkMath.RH

-- ============================================================================

namespace DkMath.RH.EulerZeta
-- #print axioms eulerZetaMag_multipliable_sigma_gt_one
-- #print axioms eulerZetaMag_pos_sigma_gt_one
end DkMath.RH.EulerZeta

-- ============================================================================