/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GNPrimeClosure
import DkMath.NumberTheory.GNRepresentationBounds
import DkMath.NumberTheory.GNDegreeFactorization
import DkMath.NumberTheory.GNPrimeTargetResidue
import DkMath.NumberTheory.GNThreeQuadratic
import DkMath.NumberTheory.GNThreePrimeArithmetic
import DkMath.NumberTheory.GNThreeHenselLift
import DkMath.NumberTheory.GNThreeHenselDepth

#print "file: DkMath.NumberTheory.GNPrime"

/-!
## GN Prime public entry point

This facade collects the elementary GN prime closure, finite positive GN
representation bounds, composite-degree factorization and prime-degree
necessity, prime-target residue filters, the degree-three discriminant
`-3`/trace-one quadratic shell, primitive cubic prime-divisor arithmetic, and
one-step and arbitrary finite-depth simple-root lifting.

This public surface is pure NumberTheory.  FLT-specific bridges, infinite
`q`-adic completions, and application endpoints remain outside this facade.
-/
