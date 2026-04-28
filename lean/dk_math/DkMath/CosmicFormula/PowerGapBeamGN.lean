/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.PowerGapBeam
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CosmicFormula.PowerGapBeamGN"

/-!
# Bridge from Power Beam to GN

This file keeps the heavier `GN` dependency out of the pure `PowerGapBeam`
module and records explicit low-degree bridges.
-/

namespace DkMath.CosmicFormula.PowerGapBeam

/-- In degree 3, the shifted Power Beam agrees with the existing cubic `GN`
    beam expression. -/
theorem powerBeam_three_shift_eq_GN {R : Type*} [CommRing R] (x u : R) :
    powerBeam 3 x (x + u) = DkMath.CosmicFormulaBinom.GN 3 u x := by
  rw [powerBeam_three]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  ring

/-- In degree 4, the shifted Power Beam agrees with the existing quartic `GN`
    beam expression. -/
theorem powerBeam_four_shift_eq_GN {R : Type*} [CommRing R] (x u : R) :
    powerBeam 4 x (x + u) = DkMath.CosmicFormulaBinom.GN 4 u x := by
  rw [powerBeam_four]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]
  ring

end DkMath.CosmicFormula.PowerGapBeam
