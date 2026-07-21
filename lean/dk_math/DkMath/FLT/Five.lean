/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Main

#print "file: DkMath.FLT.Five"

/-!
# GN5 / FLT5 exponent-five development

The public endpoint `DkMath.FLT.Five.fermatFive_no_positive_solution` proves that
positive natural numbers do not satisfy `x^5 + y^5 = z^5`. Its proof passes
through GN5 identities, five-adic factor splitting, arithmetic in the direct
coordinate golden order, unit classes, and a strict zero-sector descent.

The scope is exponent five over positive natural numbers. No claim is made here
about the general Fermat theorem, historical novelty, external peer review, or
formal identification of `GoldenInt` with a field-level ring of integers.

`Standalone.lean` is deliberately not imported here: it must remain a Mathlib-only
single-file seed for Lean Comparator Live.
-/
