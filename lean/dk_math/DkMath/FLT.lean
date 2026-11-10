/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Main    -- 旧 Facade

import DkMath.FLT.Three   -- FLT3
import DkMath.FLT.Five    -- FLT5
import DkMath.FLT.Seven   -- FLT7

import DkMath.FLT.Frey
import DkMath.FLT.FreyTwo

import DkMath.FLT.FreyBranchComparison
import DkMath.FLT.FreyCofixedBranchSwap
import DkMath.FLT.FreyCofixedCyclotomic
import DkMath.FLT.FreyCofixedImage
import DkMath.FLT.FreyCounterexample
import DkMath.FLT.FreyCriticalCentre
import DkMath.FLT.FreyDoublingDepth

import DkMath.FLT.FreyDyadicBranchSwap
import DkMath.FLT.FreyDyadicGeometry
import DkMath.FLT.FreyDyadicInertia
import DkMath.FLT.FreyDyadicNontrivial
import DkMath.FLT.FreyDyadicZeroComponent

import DkMath.FLT.FreyFiniteKernel
import DkMath.FLT.FreyFiniteKernelCollision
import DkMath.FLT.FreyFiniteKernelDegree
import DkMath.FLT.FreyFiniteKernelDepthProduct
import DkMath.FLT.FreyFiniteKernelDenominatorSupport
import DkMath.FLT.FreyFiniteKernelDiscriminantDepth
import DkMath.FLT.FreyFiniteKernelGeneration
import DkMath.FLT.FreyFiniteKernelGlobal
import DkMath.FLT.FreyFiniteKernelGoodReduction
import DkMath.FLT.FreyHnoSmallGoodPrime
import DkMath.FLT.FreyNodalSmoothTorsionExclusion
import DkMath.FLT.FreyComponentTorsionDichotomy
import DkMath.FLT.FreyDyadicComponentObstruction
import DkMath.FLT.FreyTriadicComponentObstruction
import DkMath.FLT.FreyMazurLocalInputs
import DkMath.FLT.FreyHnoSmallIndex
import DkMath.FLT.FreyHnoRegularPrime
import DkMath.FLT.FreyHnoHardCase
import DkMath.FLT.FreyTorsionTowerObstruction
import DkMath.FLT.FreyTorsionInertiaAbsorption
import DkMath.FLT.FreyCofixedTorsionExtension
import DkMath.FLT.FreyCofixedTorsionTower
import DkMath.FLT.FreyHnoThreeGood
import DkMath.FLT.FreyFiniteKernelHom
import DkMath.FLT.FreyFiniteKernelIntegralModel
import DkMath.FLT.FreyFiniteKernelLocalIntegrality
import DkMath.FLT.FreyFiniteKernelModel
import DkMath.FLT.FreyFiniteKernelNodalAll
import DkMath.FLT.FreyFiniteKernelNodalInverse
import DkMath.FLT.FreyFiniteKernelNodalReduction
import DkMath.FLT.FreyFiniteKernelNodalTransport
import DkMath.FLT.FreyFiniteKernelNoncollision
import DkMath.FLT.FreyFiniteKernelNonsingular
import DkMath.FLT.FreyFiniteKernelPointDescent
import DkMath.FLT.FreyFiniteKernelPoles
import DkMath.FLT.FreyFiniteKernelReducedHom
import DkMath.FLT.FreyFiniteKernelReduction
import DkMath.FLT.FreyFiniteKernelReductionSquare
import DkMath.FLT.FreyFiniteKernelSingularInverse
import DkMath.FLT.FreyFiniteKernelSpecialization
import DkMath.FLT.FreyFiniteKernelValuation
import DkMath.FLT.FreyFiniteKernelZeroComponent
import DkMath.FLT.FreyFiniteKernelZeroComponentAway
import DkMath.FLT.FreyFiniteKernelZeroComponentExact

import DkMath.FLT.FreyGeometricWeilPairing
import DkMath.FLT.FreyGoodReductionInertia
import DkMath.FLT.FreyInertiaTransport
import DkMath.FLT.FreyIntegralTorsionWitness
import DkMath.FLT.FreyModEightIrreducibility
import DkMath.FLT.FreyNodalReduction

import DkMath.FLT.FreyPrimeFiltration
import DkMath.FLT.FreyPrimePowerFiltration
import DkMath.FLT.FreyNonresonantInertia
import DkMath.FLT.FreyCyclotomicExtensionCharacter
import DkMath.FLT.FreyCyclotomicCharacterField
import DkMath.FLT.FreyCyclotomicKummer
import DkMath.FLT.FreyCyclotomicKummerWeight
import DkMath.FLT.FreyCyclotomicKummerArithmetic
import DkMath.FLT.FreyCyclotomicKummerClassMap
import DkMath.FLT.FreyCyclotomicKummerEquivariance
import DkMath.FLT.FreyCyclotomicKummerUnitEquivariance
import DkMath.FLT.FreyCyclotomicClassVanishing
import DkMath.FLT.FreyCyclotomicKummerSelmer
import DkMath.FLT.FreyCyclotomicKummerDecomposition
import DkMath.FLT.FreyCyclotomicKummerLocalPower
import DkMath.FLT.FreyCyclotomicConditionalSplit
import DkMath.FLT.FreyCyclotomicPrimaryLogSplit
import DkMath.FLT.FreyCyclotomicUnitSplit
import DkMath.FLT.FreyCyclotomicTowerStep
import DkMath.FLT.FreyCyclotomicConditionalTower
import DkMath.FLT.FreyCyclicTowerCharacter
import DkMath.FLT.FreyPadicTowerCharacter
import DkMath.FLT.FreyCyclicTateVector
import DkMath.FLT.FreyCyclicTateLine
import DkMath.FLT.FreyCyclicTateUnion
import DkMath.FLT.FreyCyclicTateReduction
import DkMath.FLT.FreyTateBasis
import DkMath.FLT.FreyTateCharacters
import DkMath.FLT.FreyTateCharactersModP
import DkMath.FLT.FreyTateCyclotomicDeterminant
import DkMath.FLT.FreyTateFrobenius
import DkMath.FLT.FreyTateFiniteQuotient
import DkMath.FLT.FreyTateInertiaQuotient
import DkMath.FLT.FreyTateGoodReductionCharacter
import DkMath.FLT.FreyTateResonantWitness
import DkMath.FLT.FreyTateInertiaUnipotent
import DkMath.FLT.FreyTateInertiaCharacters
import DkMath.FLT.FreyConditionalCofixedExclusion
import DkMath.FLT.FreySmoothStageAbsorption
import DkMath.FLT.FreyNarrowFailureGeometry
import DkMath.FLT.FreyCofixedArithmeticObstruction
import DkMath.FLT.FreyCandidateCofixedExclusion
import DkMath.FLT.FreyStageLocalComponent
import DkMath.FLT.FreyStageUpperQuotient
import DkMath.FLT.FreyIntersectionQuotientObstruction
import DkMath.FLT.FreyStageIntersectionGenerator
import DkMath.FLT.FreyInertiaDifferenceCharacter
import DkMath.FLT.FreyStageUpperQuotientCard
import DkMath.FLT.FreyStageUpperQuotientTopology
import DkMath.FLT.FreyInertiaCharacterFiniteImage
import DkMath.FLT.FreyWildInertia
import DkMath.FLT.FreyTameInertiaQuotient
import DkMath.FLT.FreyTameResonance
import DkMath.FLT.FreyFixedTameCharacter
import DkMath.FLT.FreyFixedInertiaH1
import DkMath.FLT.FreyInertiaH1CoefficientBoundary
import DkMath.FLT.FreyFixedH1Inflation
import DkMath.FLT.FreyFixedCoefficientSequence
import DkMath.FLT.FreyInvariantCosetObstruction
import DkMath.FLT.FreyFixedH1Connecting
import DkMath.FLT.FreyFixedH1PrimeOrder
import DkMath.FLT.FreyFixedQuotientTrivial
import DkMath.FLT.FreyFixedConnectingInjective
import DkMath.FLT.FreyFixedConnectingKernel
import DkMath.FLT.FreyConnectingKernelPrimeOrder
import DkMath.FLT.FreyConnectingKernelCertificate
import DkMath.FLT.FreyFixedDifferencePrimeOrder
import DkMath.FLT.FreyConnectingKernelSharpProfile
import DkMath.FLT.FreyConnectingKernelEvaluation
import DkMath.FLT.FreyKernelEvaluationImage
import DkMath.FLT.FreyKernelEvaluationCertificate
import DkMath.FLT.FreyKernelEvaluationConstraints
import DkMath.FLT.FreyKernelCharacterContinuity
import DkMath.FLT.FreyKernelTameDescent
import DkMath.FLT.FreyKernelCommonTameQuotient
import DkMath.FLT.FreyKernelFiniteDetector
import DkMath.FLT.FreyCommonTameFaithful
import DkMath.FLT.FreyCommonTamePGroup
import DkMath.FLT.FreyCommonTameEvaluation
import DkMath.FLT.FreyCommonTameGeneratorCriterion
import DkMath.FLT.FreyCommonTameStructureCertificate
import DkMath.FLT.FreyRadicalGeneratorCertificate
import DkMath.FLT.FreyRadicalKernelComparison
import DkMath.FLT.FreyGoodReductionTowerObstruction
import DkMath.FLT.FreyPrimeGoodFiltration
import DkMath.FLT.FreyPrimeProfile

import DkMath.FLT.FreyRationalTorsion
import DkMath.FLT.FreyRationalTorsionBounds
import DkMath.FLT.FreyRationalTorsionBridge
import DkMath.FLT.FreyRationalTorsionIdentities
import DkMath.FLT.FreyRationalTorsionIntegral
import DkMath.FLT.FreyRationalTorsionPositive
import DkMath.FLT.FreyRationalTorsionValuation
import DkMath.FLT.FreyRationalTwoPTorsion

import DkMath.FLT.FreyResidualCyclotomic
import DkMath.FLT.FreyResidualDimensionBound
import DkMath.FLT.FreyResidualDimensionCriteria
import DkMath.FLT.FreyResidualFiniteLevel
import DkMath.FLT.FreyResidualGL2
import DkMath.FLT.FreyResidualGeometry
import DkMath.FLT.FreyResidualIrreducibility
import DkMath.FLT.FreyResidualNontrivial
import DkMath.FLT.FreyResidualRankTwo
import DkMath.FLT.FreyResidualRepresentation

import DkMath.FLT.FreyShallowSlope
import DkMath.FLT.FreySmoothReductionInertia
import DkMath.FLT.FreySplitDyadic

import DkMath.FLT.FreyStableLine
import DkMath.FLT.FreyStableLineDiscriminantCriterion
import DkMath.FLT.FreyStableLineLocalGlobal

import DkMath.FLT.FreyTorsionAllCard
import DkMath.FLT.FreyTorsionPrimePower

import DkMath.FLT.FreyUnramifiedAway
import DkMath.FLT.FreyValuationArithmetic

import DkMath.FLT.FreyWeilBicharacter
import DkMath.FLT.FreyWeilCharacter
import DkMath.FLT.FreyWeilFunction
import DkMath.FLT.FreyWeilGalois
import DkMath.FLT.FreyWeilGeometry
import DkMath.FLT.FreyWeilTransport
import DkMath.FLT.FreyWeilValuation

import DkMath.FLT.GEisensteinBridge

import DkMath.FLT.Kummer

import DkMath.FLT.PrimeDepthBridge
import DkMath.FLT.PrimeProvider

import DkMath.FLT.QuadraticEssence

import DkMath.FLT.Samples

import DkMath.FLT.FreyTailKernelVanishing

import DkMath.FLT.FreyCommonProjectionTopology
import DkMath.FLT.FreyRadicalFiniteDetection
import DkMath.FLT.FreyRadicalKernelClosure
import DkMath.FLT.FreyCommonTameCyclicClosure

import DkMath.FLT.FreyContinuousKernelCharacters
import DkMath.FLT.FreyContinuousConnectingComparison
import DkMath.FLT.FreyContinuousTameInflation
import DkMath.FLT.FreyCyclicKernelBalancedProfile
import DkMath.FLT.FreyContinuousObstructionCertificate

import DkMath.FLT.FreyGlobalUpperCoefficient
import DkMath.FLT.FreyGlobalInertiaRestriction
import DkMath.FLT.FreyDecompositionFixedCoefficient
import DkMath.FLT.FreyDecompositionCocycleCovariance
import DkMath.FLT.FreyRelativeGlobalOrigin
import DkMath.FLT.FreyRelativeGlobalObstructionCertificate

import DkMath.FLT.FreyDecompositionQuotientAction
import DkMath.FLT.FreyConnectingDecompositionEquivariance
import DkMath.FLT.FreyKernelDecompositionEvaluation
import DkMath.FLT.FreyResidueDecompositionAction
import DkMath.FLT.FreyKernelFrobeniusCovariance
import DkMath.FLT.FreyKernelFrobeniusFixedCriterion
import DkMath.FLT.FreyDecompositionInvariantObstruction

import DkMath.FLT.FreyPrimeOrderGeneratorValue
import DkMath.FLT.FreyResonantFrobeniusSigns
import DkMath.FLT.FreyDecompositionOrbitContinuity
import DkMath.FLT.FreyDecompositionCoefficientSequence
import DkMath.FLT.FreyDecompositionConnectingCocycle
import DkMath.FLT.FreyDecompositionConnectingRestriction
import DkMath.FLT.FreyResonantDecompositionLift

import DkMath.FLT.FreyClosedKernelStabilizer
import DkMath.FLT.FreyDenseKernelFixed
import DkMath.FLT.FreyFrobeniusLiftIndependence
import DkMath.FLT.FreyDenseResonantFixed
import DkMath.FLT.FreyDenseResonantLift

import DkMath.FLT.FreyFiniteDecompositionAction
import DkMath.FLT.FreyOpenDecompositionActionKernel
import DkMath.FLT.FreyFiniteFrobeniusImage
import DkMath.FLT.FreyFiniteImageFixedCriterion
import DkMath.FLT.FreyFiniteImageResonantLift
import DkMath.FLT.FreyResidueFiniteActionFactor
import DkMath.FLT.FreyKernelOrbitCriterion
import DkMath.FLT.FreyOrbitResonantLift

#print "file: DkMath.FLT"

set_option linter.style.longLine false

/-!
# DkMath FLT historical broad aggregator

`DkMath.FLT` is a broad compatibility/research aggregator that predates the
independent completed exponent-three public surface.  It still imports legacy
`Main`, Kummer/provider research, FLT5, FLT7 research, and related bridge
modules, so it is intentionally **not** the canonical discovery import for the
current standalone FLT3 proof.

For completed exponent-specific public results, prefer explicit imports:

```text
> import DkMath.FLT.Three
> import DkMath.FLT.Five
```

with endpoints:

- `DkMath.FLT.Three.fermatThree_no_positive_solution`
- `DkMath.FLT.Five.fermatFive_no_positive_solution`

For the current odd-prime generalization architecture, see `DkMath.FLT.Prime.*`
and `docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`.

For neutral reusable mathematics extracted from FLT and other research owners,
prefer `DkMath.Lib` where an appropriate promoted API exists.

No import semantics are changed by this documentation note: in particular,
`DkMath.FLT.Three` remains an explicit independent import rather than being
silently added to this historical aggregator.
-/
