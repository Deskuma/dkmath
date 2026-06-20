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

#print "file: DkMath.Analysis.DkReal"

/-!
# DkReal approximation layer

Public entry point for the complete Route B algebraic checkpoint:

* `GapInterval` gives exact rational closed intervals;
* `DkReal` gives nested interval sequences of vanishing width;
* `DkReal.Equiv` identifies representations of vanishing separation;
* `DkNNReal` packages nonnegativity;
* `DkNNRealQ` is the quotient-backed nonnegative `CommSemiring`.

All endpoint operations in this import tree remain computable. No represented
limit in Mathlib's `Real` or `NNReal` is selected here.

`DkReal.Order` defines a quotient-compatible asymptotic order and installs a
`PartialOrder` and Mathlib's semiring-level `IsOrderedRing` predicate on
`DkNNRealQ`. Addition, nonnegative multiplication, and natural powers are
monotone, and zero is least.

[TODO: totality] Prove totality internally from nested-interval geometry:
eventual strict left separation, eventual strict right separation, or
persistent overlap. The first two branches give one order direction; the
overlap branch gives `Equiv`.

[TODO: linear-order] Install no `LinearOrder` or linear ordered semiring API
until representative totality has been proved and lifted through the quotient.

[TODO: canonical-order] Treat `x ≤ y ↔ ∃ z, y = x + z` as an independent
problem. It is not a consequence of the current ordered-semiring compatibility
alone.

[TODO: semantic-bridge] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
chosen evaluation is independent of representatives. Such evaluation may
legitimately be `noncomputable`.

[TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
endpoint products and belongs outside the current nonnegative API.
-/
