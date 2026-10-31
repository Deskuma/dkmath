/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalCentre
import DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

#print "file: DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre"

/-!
# Reducing a critical centre to a rational singular centre

`EllipticCriticalCentre.CriticalCentre` is a valuation-theoretic object: its
coordinates live in the generic field but are integral, and its equation
defect becomes zero after reduction.  The nodal cardinality argument instead
asks for an honest singular point of the reduced cubic.

This file is the exact bridge between those two interfaces.  Reducing the two
integral coordinates of a `CriticalCentre` produces a `SingularCentre` of the
residue curve.  Thus the slope-coordinate bound applies whenever a critical
centre on the generic fibre has already been supplied.

The construction does not claim that multiplicative reduction alone has
produced a `CriticalCentre`; it only preserves the already formalized
critical-centre data through reduction.
-/

namespace DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre

open WeierstrassCurve IsLocalRing
open EllipticCriticalCentre EllipticNodalSmoothCard

variable {L : Type*} [Field L] {A : ValuationSubring L}

/-- [DkMath.Lib] The reduction of a valuation-theoretic critical centre is a
rational singular centre of the residue cubic.  This packages the equation
and both vanishing partial derivatives in precisely the form used by the
slope-coordinate cardinality bound. -/
noncomputable def singularCentreOfCriticalCentre (W : WeierstrassCurve A)
    (C : CriticalCentre A (W.map A.subtype)) :
    SingularCentre (W.map (residue A)) := by
  let x : A := ⟨C.x, C.x_mem⟩
  let y : A := ⟨C.y, C.y_mem⟩
  have hC := C.residue_singular W
  have hs := hC.2
  rw [Affine.nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hX, hY⟩ := hs hC.1
  exact
    { x := residue A x
      y := residue A y
      equation := hC.1
      derivativeX := hX
      derivativeY := hY }

/-!
## Cardinality corollaries

The preceding conversion is deliberately separated from these consequences:
the first is useful over any finite residue field, while the second is the
positive-cardinality input needed for prime-divisibility arguments.
-/

/-- [DkMath.Lib] A critical centre gives the splitness-free bound
`#E_sm(k) ≤ #k + 1` on the residue cubic. -/
theorem natCard_points_le_card_add_one_of_criticalCentre
    [Finite (ResidueField A)] [Fintype (ResidueField A)]
    (W : WeierstrassCurve A) (C : CriticalCentre A (W.map A.subtype)) :
    Nat.card (W.map (residue A)).toAffine.Point ≤ Fintype.card (ResidueField A) + 1 :=
  natCard_points_le_card_add_one (singularCentreOfCriticalCentre W C)

/-- [DkMath.Lib] The residue smooth point type remains nonempty when supplied
through a critical centre; the point at infinity accounts for this positivity. -/
theorem natCard_points_pos_of_criticalCentre [Finite (ResidueField A)]
    (W : WeierstrassCurve A) (C : CriticalCentre A (W.map A.subtype)) :
    0 < Nat.card (W.map (residue A)).toAffine.Point :=
  natCard_points_pos (singularCentreOfCriticalCentre W C)

end DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre
