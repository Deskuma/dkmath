/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Interval
import DkMath.Analysis.DkReal.Basic
import DkMath.Analysis.DkReal.Pow
import DkMath.Analysis.DkReal.PowBound
import DkMath.Analysis.DkReal.Arithmetic
import DkMath.Analysis.DkReal.Equiv
import DkMath.Analysis.DkReal.DkNNReal
import DkMath.Analysis.DkReal.DkNNRealQ
import DkMath.Analysis.DkReal.Order
import DkMath.Analysis.DkReal.CanonicalOrder
import DkMath.Analysis.DkReal.Semantic

#print "file: DkMath.Analysis.DkReal"

/-!
# DkReal approximation layer

Public entry point for the complete Route B algebraic checkpoint:

* `GapInterval` gives exact rational closed intervals;
* `DkReal` gives nested interval sequences of vanishing width;
* `DkReal.Equiv` identifies representations of vanishing separation;
* `DkNNReal` packages nonnegativity;
* `DkNNRealQ` is the quotient-backed nonnegative ordered `CommSemiring`;
* `DkReal.CanonicalOrder` extracts nonnegative Gap universes.
* `DkReal.Semantic` gives the noncomputable bridge to Mathlib's `Real`.

All endpoint operations in the representation modules remain computable. The
publicly imported optional `Semantic` module selects a Mathlib `Real` value
noncomputably; it does not alter the computable representation operations.

`DkReal.Order` defines a quotient-compatible asymptotic order and installs a
`PartialOrder` and Mathlib's semiring-level `IsOrderedRing` predicate on
`DkNNRealQ`. Addition, nonnegative multiplication, and natural powers are
monotone, and zero is least.

Totality is proved internally from nested-interval geometry. If a finite
strict left separation is witnessed, it persists. Otherwise the reverse order
defect is bounded by a vanishing interval width.

Canonical order is also constructive at the representation level. From
`x ≤ y`, `CanonicalOrder` extracts a computable nonnegative Gap `z` such that
`y = x + z` in the quotient. No subtraction operation is added to
`DkNNRealQ`.

The strict-order kernel classifies this known Gap: wrapper strictness is
equivalent both to finite left separation and to a positive lower endpoint of
the canonical Gap at some stage. This keeps the design in the same
`Big = (Core + Beam) + Gap` pattern.

Strict order has now descended to the quotient. Addition preserves it by
moving to a sufficiently precise stage. Multiplication preserves it for a
strictly positive factor by transforming the canonical Gap from `z` to
`z * a`; the zero-factor branch collapses that Gap.

`CanonicalOrder` installs Mathlib's `IsStrictOrderedRing`. Its requirements
match the proved API: cancellative ordered addition, nontriviality, and strict
multiplication by positive factors. It requires neither additive inverses nor
a linear order.

[DESIGN: linear-order] Retain `PartialOrder` plus `Std.Total`. Mathlib's
`LinearOrder` requires decidable comparison and equality, but no terminating
decision procedure for asymptotic interval order is currently available.
Classical comparison should therefore remain an explicit local choice.

`DkReal.Semantic` selects the lower-endpoint supremum, proves that it is the
unique real point lying in every approximation interval, and proves invariance
under representation equivalence. Its quotient map preserves rational
constants, addition, multiplication, natural powers, and canonical order.

[TODO: semantic-order-reflection] Prove that an inequality between semantic
values reconstructs the canonical quotient order, without adding decidable
comparison.

[IMPLEMENTED: semantic-cf2d-action] `DkReal.SemanticCF2D` transports unit
kernels to `Real`, derives the Pythagorean coordinate identity, and applies
the resulting kernel as a real square-mass-preserving action. Transported
actions compose through real-side kernel products and restrict to every real
square-mass level set. Real-side conjugation supplies inverse actions, so
these maps are equivalences of the plane and of each level set. Their finite
iterates generate forward orbits of constant square mass. Periodic points and
finite action order are expressed through Mathlib's standard discrete-dynamics
API.

[TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
signed arithmetic. Defer them until a signed DkReal layer exists.

[TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
endpoint products and belongs outside the current nonnegative API.
-/
