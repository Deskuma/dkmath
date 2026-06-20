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
`PartialOrder` on `DkNNRealQ`.

[TODO] Prove additive and multiplicative monotonicity, then determine whether
the quotient order is total before installing ordered-semiring typeclasses.

[TODO] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
chosen evaluation is independent of representatives. Such evaluation may
legitimately be `noncomputable`.

[TODO] General signed multiplication requires the minimum and maximum of four
endpoint products and belongs outside the current nonnegative API.
-/
