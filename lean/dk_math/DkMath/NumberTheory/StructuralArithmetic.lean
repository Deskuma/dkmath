/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PowerGauge
import DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
import DkMath.NumberTheory.StructuralArithmetic.InterPeriod

#print "file: DkMath.NumberTheory.StructuralArithmetic"

/-!
# DkMath.NumberTheory.StructuralArithmetic

Public aggregation point for the structure-preserving / projection vocabulary
used to connect KUS, prime coordinates, DHNT scaling, Cosmic Formula GN, and
power-gauge quotient views.

The implementation contains the period/exponent projection kernel, its first
concrete specialization to ordinary prime-valuation coordinates, and canonical
forgetting from period `d` to period `m` when `m ∣ d`. Further bridges are
intentionally added here only after their local modules are stable.
-/
