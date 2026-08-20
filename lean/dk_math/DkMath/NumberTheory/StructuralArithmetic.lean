/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PowerGauge
import DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
import DkMath.NumberTheory.StructuralArithmetic.InterPeriod
import DkMath.NumberTheory.StructuralArithmetic.KUSObservation
import DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
import DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
import DkMath.NumberTheory.StructuralArithmetic.GNBridge
import DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge

#print "file: DkMath.NumberTheory.StructuralArithmetic"

/-!
# DkMath.NumberTheory.StructuralArithmetic

Public aggregation point for the structure-preserving / projection vocabulary
used to connect KUS, prime coordinates, DHNT scaling, Cosmic Formula GN, and
power-gauge quotient views.

The implementation contains the period/exponent projection kernel, its first
concrete specialization to ordinary prime-valuation coordinates, canonical
forgetting from period `d` to period `m` when `m ∣ d`, and an explicit observer
bridge from retained KUS support to projected coordinates. The GN bridge
reuses the existing PrimitiveBeam divisibility theorem, keeps finite-scale
freshness explicit, and transports the Phase-E finite escape through the exact
degree-five `GN5`/generic-`GN` identity.
The golden-unit bridge adds a relation-valued fifth-power sector observer,
its Red Ribbon absorption law, and a receiver for stripped FLT5 packets.
-/
