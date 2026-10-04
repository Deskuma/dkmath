/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.Focus
import DkMath.NumberTheory.GapFocusing.Phase
import DkMath.NumberTheory.GapFocusing.Degree
import DkMath.NumberTheory.GapFocusing.UnitGauge
import DkMath.NumberTheory.GapFocusing.Successor
import DkMath.NumberTheory.GapFocusing.Support
import DkMath.NumberTheory.GapFocusing.PolynomialSuccessor
import DkMath.NumberTheory.GapFocusing.SuccessorGauge

#print "file: DkMath.NumberTheory.GapFocusing"

/-!
# Gap focusing: exact algebra and the arithmetic unit-class boundary

`Focus` gives the unique polynomial quotient and constant defect, `Phase`
identifies GN with the product of nontrivial phases in a splitting domain,
and `Degree` characterizes prime degree by irreducibility over `ℤ` at `u = 1`.
`UnitGauge` retains the extra extraction and normalization data needed for
unit classes modulo powers; a phase decomposition alone does not provide them.

`Successor` and `Support` give adjacent-degree recurrences and primitive-pair
coprimality. `PolynomialSuccessor` provides polynomial Bézout witnesses,
disjoint cyclotomic layers, and a quotient-ring CRT. `SuccessorGauge` connects
the existing unit-class relation to the separate power-subgroup CRT.

See `docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-001.md` for
the source audit, assumptions, and interpretation boundaries.
The adjacent-degree extension is documented in the same directory's
`report-002.md`.
-/
