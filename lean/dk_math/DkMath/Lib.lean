/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
import DkMath.Lib.Basic
import DkMath.Lib.Algebra.PowerSubgroup
import DkMath.Lib.Algebra.UnitPowerClass
import DkMath.Lib.Algebra.OddPowerRecovery
import DkMath.Lib.TwoChannel
import DkMath.Lib.NumberTheory.PadicValNat
import DkMath.Lib.NumberTheory.FreyGapCubic
import DkMath.Lib.NumberTheory.GNFreyDiscriminant
import DkMath.Lib.NumberTheory.FreyPrimeValuation
import DkMath.Lib.NumberTheory.FreyLocalReduction
import DkMath.Lib.NumberTheory.HomogeneousPowerQuotient
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.Lib.NumberTheory.TraceOneLatticeLanding
import DkMath.Lib.NumberTheory.FiniteFreeLatticeLanding
import DkMath.Lib.NumberTheory.QuadraticResidueType
import DkMath.Lib.NumberTheory.PolynomialHenselDigit
import DkMath.Lib.NumberTheory.TraceOnePowerLanding
import DkMath.Lib.NumberTheory.EisensteinCoordinates
import DkMath.Lib.NumberTheory.EisensteinCyclotomic
import DkMath.Lib.NumberTheory.QuinticGoldenNorm
import DkMath.Lib.NumberTheory.EisensteinLatticeLanding
import DkMath.Lib.NumberTheory.SquarefreePowerFactor
import DkMath.Lib.Cosmic.GTail
import DkMath.Lib.Cosmic.GNProductDegree
import DkMath.Lib.Cosmic.GNSourceTransport
import DkMath.Lib.Cosmic.GNPhaseThreeTerm
import DkMath.Lib.Algebra.RootUnitGauge
import DkMath.Lib.Cosmic.CyclicDeterminant
import DkMath.Lib.Cosmic.GTailCyclotomic
import DkMath.Lib.Cosmic.GTailPascal
import DkMath.Lib.Cosmic.GTailBoundary
import DkMath.Lib.Cosmic.GTailNat
import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.Lib.Cosmic.GTailPadic
import DkMath.Lib.Cosmic.GTailSelection
import DkMath.Lib.Cosmic.GTailFactor
import DkMath.Lib.Cosmic.GTailTransport
import DkMath.Lib.Cosmic.CoreNested
import DkMath.Lib.Cosmic.CoreNestedTransport
import DkMath.Lib.NumberTheory.RamifiedGNPhaseBridge
import DkMath.Lib.NumberTheory.CyclotomicPhaseCoefficientRigidity
import DkMath.Lib.NumberTheory.SparsePhaseObstruction
import DkMath.Lib.NumberTheory.RegularKummer.Cyclotomic.UnitConjugation
import DkMath.Lib.NumberTheory.IdealPowerObstruction
import DkMath.Lib.NumberTheory.PhaseClassPacket
import DkMath.Lib.NumberTheory.PhaseObstructionTransport
import DkMath.Lib.NumberTheory.IdealGaloisTransport
import DkMath.Lib.NumberTheory.GaloisPhaseObstructionTransport
import DkMath.Lib.NumberTheory.GaloisPhaseOrbitNorm
import DkMath.Lib.NumberTheory.GaloisIdealNorm
import DkMath.Lib.NumberTheory.CyclotomicClassNorm
import DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
import DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
import DkMath.Lib.NumberTheory.Cyclotomic37CharacterTransport
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import DkMath.Lib.NumberTheory.EllipticTorsionContinuity
import DkMath.Lib.NumberTheory.EllipticTorsionGaloisStable
import DkMath.Lib.NumberTheory.EllipticTorsionStandardEquiv
import DkMath.Lib.NumberTheory.EllipticTorsionRankTwo
import DkMath.Lib.NumberTheory.EllipticTorsionFiniteLevel
import DkMath.Lib.NumberTheory.EllipticDivisionSequence
import DkMath.Lib.NumberTheory.EllipticDivisionUniversal
import DkMath.Lib.NumberTheory.EllipticDivisionCoordinates
import DkMath.Lib.NumberTheory.EllipticDivisionMultiplication
import DkMath.Lib.NumberTheory.EllipticTorsionFinite
import DkMath.Lib.NumberTheory.EllipticTorsionCardBound
import DkMath.Lib.NumberTheory.EllipticTorsionDimensionBound
import DkMath.Lib.NumberTheory.EllipticTorsionNontrivial
import DkMath.Lib.NumberTheory.EllipticTorsionRootCount
import DkMath.Lib.NumberTheory.EllipticTorsionDimensionCriteria
import DkMath.Lib.NumberTheory.EllipticTwoTorsionRank
import DkMath.Lib.Algebra.RationalPolynomialFiber
import DkMath.Lib.NumberTheory.EllipticMultiplicationCoordinates
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber
import DkMath.Lib.RepresentationTheory.InvariantLine
import DkMath.Lib.RepresentationTheory.MatrixRealization
import DkMath.Lib.NumberTheory.EllipticTorsionGL2
import DkMath.Lib.RepresentationTheory.PascalDifference
import DkMath.Lib.NumberTheory.FreyTwoArithmetic
import DkMath.Lib.NumberTheory.UnitObstructionPacket
import DkMath.Lib.NumberTheory.BernoulliPrime37
import DkMath.Lib.Cosmic.GNPrime37
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.KummersLemma
import DkMath.Lib.NumberTheory.CyclotomicElevenPID
import DkMath.Lib.NumberTheory.CyclotomicThirteenPID
import DkMath.Lib.Cosmic.GTailSeven
import DkMath.Lib.Cosmic.GTailSevenArithmetic

#print "file: DkMath.Lib"

/-!
# DkMath.Lib

This is the development-side public entrance for reusable library components.

Importing `DkMath.Lib` exposes the currently promoted `DkMath.Lib.*` layer
without importing the whole experimental `DkMath` workspace.
-/

namespace DkMath.Lib

end DkMath.Lib
