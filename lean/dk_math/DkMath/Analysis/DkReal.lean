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

All endpoint operations in this import tree remain computable. No represented
limit in Mathlib's `Real` or `NNReal` is selected here.

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

[TODO: strict-arithmetic] Prove preservation by addition and by multiplication
with a strictly positive factor before selecting a strict-order typeclass.

[TODO: linear-order] Decide whether the now-proved quotient totality should be
packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
plus `Std.Total` so that decidable comparison remains an explicit choice.

[TODO: semantic-bridge] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
chosen evaluation is independent of representatives. Such evaluation may
legitimately be `noncomputable`.

[TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
endpoint products and belongs outside the current nonnegative API.
-/
