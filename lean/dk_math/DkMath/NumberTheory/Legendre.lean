/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Frontier
import DkMath.NumberTheory.Legendre.CenteredPair
import DkMath.NumberTheory.Legendre.CenteredPacketTriangle
import DkMath.NumberTheory.Legendre.CenteredPacketDiamond
import DkMath.NumberTheory.Legendre.CenteredPacketClique4
import DkMath.NumberTheory.Legendre.CoprimeSeatCapacity
import DkMath.NumberTheory.Legendre.OldSupportCapacity
import DkMath.NumberTheory.Legendre.OldSupportGcd
import DkMath.NumberTheory.Legendre.FreshCollisionMatching
import DkMath.NumberTheory.Legendre.FreshCollisionRepair
import DkMath.NumberTheory.Legendre.ActivePrimeCapacity
import DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity
import DkMath.NumberTheory.Legendre.ParitySafeWavePruning
import DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
import DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
import DkMath.NumberTheory.Legendre.ParitySafeMobiusWave
import DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
import DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
import DkMath.NumberTheory.Legendre.ParitySafePairResidual
import DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate
import DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor
import DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge
import DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
import DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival

#print "file: DkMath.NumberTheory.Legendre"

/-!
## Legendre application facade

Public entry point for the square-anchored finite-prime localization stack.
The implementation is organized by dependency-ordered modules; this facade
preserves the historical import path and declaration namespace.  The current
formalization remains a bounded finite-arithmetic framework and does not add
a proof of Legendre's conjecture.
-/
