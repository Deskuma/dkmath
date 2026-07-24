/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticBridge
import DkMath.FLT.Seven.AxisDivisibility
import DkMath.FLT.Seven.AxisPowerRoll
import DkMath.FLT.Seven.AxisDepth
import DkMath.FLT.Seven.PrimitiveCyclotomicDepth
import DkMath.FLT.Seven.CounterexampleRouting
import DkMath.FLT.Seven.QuadraticResidualPacket
import DkMath.FLT.Seven.QuadraticCoprimeFactor
import DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
import DkMath.FLT.Seven.SeventhPowerCoordinates
import DkMath.FLT.Seven.CoordinateNormalForm
import DkMath.FLT.Seven.ModSevenSectors
import DkMath.FLT.Seven.AwaySecondCoordinateLoad
import DkMath.FLT.Seven.AwayValuationTransfer
import DkMath.FLT.Seven.CubicSecondCoordinateSplit
import DkMath.FLT.Seven.CoprimeTripleRouting
import DkMath.FLT.Seven.DescentClosureAudit
import DkMath.FLT.Seven.FirstCoordinateRemainders
import DkMath.FLT.Seven.RoutingSevenPivot
import DkMath.FLT.Seven.FirstCoordinateRoutingAudit
import DkMath.FLT.Seven.RoutingLocalSystems
import DkMath.FLT.Seven.RoutingLocalSolubility
import DkMath.FLT.Seven.LocalObstructionAudit
import DkMath.FLT.Seven.SpecializedPrimeAddress
import DkMath.FLT.Seven.PrimePowerCellSystems
import DkMath.FLT.Seven.PrimePowerCellSolubility
import DkMath.FLT.Seven.PrimePowerCellAudit
import DkMath.FLT.Seven.PrimePowerUnitOrbit
import DkMath.FLT.Seven.PrimePowerOrbitAudit
import DkMath.FLT.Seven.SevenPivotDescentAudit
import DkMath.FLT.Seven.SevenBaseLayerQuotient
import DkMath.FLT.Seven.SevenBaseFirstOrderModSeven
import DkMath.FLT.Seven.SevenBaseFirstOrderLinearization
import DkMath.FLT.Seven.SevenBaseUnitSectorClassification
import DkMath.FLT.Seven.SevenBaseLoadQuotient
import DkMath.FLT.Seven.SevenBaseTerminalPacket
import DkMath.FLT.Seven.SevenBaseTerminalWeightedBridge
import DkMath.FLT.Seven.SevenBaseTerminalLoadDivisibility
import DkMath.FLT.Seven.SevenBaseTerminalEndpointSeparation
import DkMath.FLT.Seven.SevenBaseTerminalCarrierRouting
import DkMath.FLT.Seven.SevenBaseTerminalFixedRouting
import DkMath.FLT.Seven.SevenBaseTerminalPrimeAddress
import DkMath.FLT.Seven.SevenBaseTerminalRootLoadAddress
import DkMath.FLT.Seven.SevenBaseTerminalPrimeCoordinate
import DkMath.FLT.Seven.SevenBaseTerminalPrimeCellCoordinate
import DkMath.FLT.Seven.SevenBaseTerminalOriginalRoutingProjection
import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeAddress
import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeDepth
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerClassification
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerOrbit
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerScaleProjection
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerPairScaleGluing
import DkMath.FLT.Seven.SevenBaseTerminalPrimeSupport
import DkMath.FLT.Seven.SevenBaseTerminalPrimeScaleFamily
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleGluing
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleReduction
import DkMath.FLT.Seven.SevenBaseTerminalCubicRootLoadModulus
import DkMath.FLT.Seven.SevenBaseTerminalAudit

#print "file: DkMath.FLT.Seven"

/-!
# FLT7 quadratic magic core

This facade exposes the proved discriminant `-7` norm, seventh cyclotomic
coordinate bridge, cubic second-coordinate split, the resulting coprime
routing, and the first-residue local-solubility audit.  Every actual non-seven
local witness is classified into an explicitly soluble model family; this does
not rule out stronger local or global obstructions.  On actual away packets,
outer factor coprimality also gives each prime a unique cell address and
isolates its exact row and column depth.  Every such address is classified at
its complete non-seven prime-power cell depth using unit-based
local systems over `ZMod (q^e)` and nine explicit soluble families.  This
prime-power classification is still local to one specialized address and does
not provide simultaneous signed reconstruction.  Moreover, every actual
full-depth solution is exactly a weight-(3,7) unit scaling of its canonical
explicit model.  Independently obtained local scales are not claimed to glue
globally.  The facade canonically indexes the finite support of primes dividing
the terminal cubic-root load and chooses one complete local scale packet over
every supported prime.  Their complete local moduli are pairwise coprime, and
the full and partial product-modulus APIs needed for finite induction are
available.  Finite CRT synchronizes all local scale residues into one unit
modulo their product, with explicit local reduction maps compatible with the
weight-three and weight-seven coordinate operations.  Compatibility of the
local canonical models is not claimed.  Each local complete exponent is also
identified with the corresponding prime's exact adic exponent in the full
terminal cubic-root load.
The unique seven-primary cell is reduced at its complete `7^k`
depth, including its nonzero top ramified kernel and base/lifted split.  At
terminal depth one, the facade also exports the exact carrier, residual,
endpoint, first-order, signed-kernel, and cubic-load quotient layers, together
with their row-sensitive `ZMod 7` linearization and the checked row-`Y`
mod-`49` shadow showing that a bare local congruence obstruction is insufficient.
The terminal arithmetic exclusion and lifted signed reconstruction remain
explicit open obligations.  The strict away depth drop is conditional on an
explicit `AwayDescentClosureProvider`; no FLT7 contradiction or recursive
closure is claimed.
-/
