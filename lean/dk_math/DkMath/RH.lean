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
import DkMath.Analysis.MellinQuadraticGramKernel
import DkMath.RH.CFBRCBridge
import DkMath.RH.CFBRC.OffCriticalExclusion
import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import DkMath.RH.CFBRC.PrimeMirrorEnergy
import DkMath.RH.CFBRC.PrimeMirrorEtaBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy
import DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
import DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
import DkMath.RH.CFBRC.PascalPrimePowerModeBridge
import DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
import DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge
import DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
import DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
import DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
import DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge
import DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
import DkMath.RH.CFBRC.MellinCenteredMirrorAdapter
import DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
import DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import DkMath.RH.CFBRC.PascalCenteredXiSafeRadiusAnnulusBridge
import DkMath.RH.CFBRC.PascalCenteredXiMellinWeightedOuterContourBridge
import DkMath.RH.CFBRC.PascalCenteredXiMellinSecondDifferenceBridge
import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge
import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourGeometry
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaSingularityLedger
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourTransport
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaRectangleResidueTransport
import DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
import DkMath.RH.CFBRC.PascalCenteredXiFiniteRectangleResidueAssembly
import DkMath.RH.CFBRC.PascalCenteredXiPrimeRightEdgeTransport
import DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
import DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideMirrorAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge
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
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientEventualSign
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjectionTail
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameVariation
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGaugeAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockAlignment
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockChord
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockProjection
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelQuantitativeMargin
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairQuantitativeMargin
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairNormMarginComparison
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockMarginDomination
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFiniteBlockCertificate
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockGeometry
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockCertificate
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelCorrectionTailBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingProjectionTailMargin
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityBlock
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairMarginPowerLowerBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominationAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCosineLossBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportSignAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedDefectTailSplit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedTailIntegral
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameEtaTailEulerHalf
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePowerTailAbelian
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelClosureDecision
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameExactGaugeObstruction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFixedLimitObstruction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordCollapseCriterion
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMirrorInvolutionAsymptoticAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameConjugationAsymptoticAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFunctionalEquationOrbitAsymptoticAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingRealLine
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionRoadmap
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameThreeElementAssimilationBridge
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
