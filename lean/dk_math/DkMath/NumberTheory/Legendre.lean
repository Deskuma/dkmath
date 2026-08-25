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

#print "file: DkMath.NumberTheory.Legendre"

/-!
## Legendre application facade

Public entry point for the square-anchored finite-prime localization stack.
The implementation is organized by dependency-ordered modules; this facade
preserves the historical import path and declaration namespace.  The current
formalization remains a bounded finite-arithmetic framework and does not add
a proof of Legendre's conjecture.
-/
