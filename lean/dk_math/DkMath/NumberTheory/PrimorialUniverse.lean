/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape
import DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement
import DkMath.NumberTheory.PrimorialUniverse.CommonLattice
import DkMath.NumberTheory.PrimorialUniverse.UnitIntersectionClassification
import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
import DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor

#print "file: DkMath.NumberTheory.PrimorialUniverse"

/-!
# Primorial Unit Universe

Public entry point for the finite reservation, integer unit-coordinate, and
coprime common-lattice and two-unit intersection-classification layers.  The current checkpoints expose exact
Euclidean escape for a finite set of ordinary `Nat.Prime`s, synchronized
positive-real refinement of natural coordinates, the canonical fiber
`(m,n) = (a*t,b*t)` of two synchronized units, the equivalence between
positive intersection and integer commensurability, and the finite
prime-scale synchronization period.  It now also exposes the one-period
wheel survivor Finset and its exact product-period reflection.  Rational/
irrational classification, next-prime wheel lifts, PowerSwap, and Legendre
consumers belong to later checkpoints.
-/
