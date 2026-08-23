/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
import DkMath.NumberTheory.Primitive.FinitePrimeWorld
import DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement
import DkMath.NumberTheory.Primitive.PrimeWorldResidues
import DkMath.NumberTheory.Primitive.PHZ30
import DkMath.NumberTheory.Primitive.SquareBody

#print "file: DkMath.NumberTheory.Primitive"

/-!
## Primitive Structure public entry point

This module collects the finite-world direction semantics and the generic
natural-number square-Body closure.  Application-specific providers, such as
the square-anchored support escape used by Legendre, remain in their own
modules.
-/
