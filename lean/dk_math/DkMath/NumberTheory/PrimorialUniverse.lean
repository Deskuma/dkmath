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
import DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift
import DkMath.NumberTheory.PrimorialUniverse.WheelReplication
import DkMath.NumberTheory.PrimorialUniverse.WheelProjection
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSign
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSignCRT
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiberProjection
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSurvivorSubcover

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
wheel survivor Finset and its exact product-period reflection, together with
the per-old-survivor fresh-prime lift, unique-deletion, and global replication
layers.  It also exposes the canonical modulo projection from an enlarged
wheel, its constant `(q - 1)` fibers, and its compatibility with reflection.
The square-anchor and fixed-shell finite orbit modulo the wheel period is also
available, together with reservation/projection equivalence and fresh-prime
nested coherence.  These provider-side statements remain independent of the
Legendre application layer.
The CRT-generated one-period square-anchor phase fiber is also available: for
a coprime anchor its cardinality is exactly `2 ^ (S.erase 2).card`, with the
prime `2` excluded from the sign index.
Fresh-prime projection of these fibers is also exported: an odd fresh prime
gives an exact two-sheet finite cover, while fresh `2` contributes no new sign
degree.
The coprime phase fiber is also exposed as a subcover of the finite wheel
survivors, including the `q = 3` equality and the strict two-of-`(q - 1)`
comparison for fresh primes above `3`.
Rational/irrational classification, square-anchor and Legendre consumers,
PowerSwap, and analytic consumers belong to later checkpoints.
-/
