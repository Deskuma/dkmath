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

#print "file: DkMath.FLT.Seven"

/-!
# FLT7 quadratic magic core

This facade exposes the proved discriminant `-7` norm and seventh cyclotomic
coordinate bridge.  It contains no FLT7 theorem, descent, or factorization
structure beyond the explicit identities in `Seven.QuadraticBridge`.
-/
