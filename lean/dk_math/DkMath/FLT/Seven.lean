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

#print "file: DkMath.FLT.Seven"

/-!
# FLT7 quadratic magic core

This facade exposes the proved discriminant `-7` norm, seventh cyclotomic
coordinate bridge, cubic second-coordinate split, and the resulting coprime
routing audit.  The strict away depth drop is conditional on an explicit
`AwayDescentClosureProvider`; no FLT7 contradiction or recursive closure is
claimed.
-/
