/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPacket

#print "file: DkMath.FLT.Seven.SevenBaseTerminalAudit"

namespace DkMath.FLT.Seven

/--
A checked row-`Y` residue shadow at depth one.

This is deliberately not an integral `CounterexamplePack`.  It records that the
naive congruence data through modulus `49`, together with the visible primitive
and cubic nonvanishing conditions modulo `7`, is locally consistent.  Hence a
terminal exclusion must use the exact quotient packet rather than a bare
mod-`49` obstruction.
-/
theorem sevenBase_rowY_mod49_shadow :
    let u : ℤ := -24
    let v : ℤ := -24
    let y : ℤ := 7
    let z : ℤ := 40
    (7 : ℤ) ∣ y ∧ ¬ (49 : ℤ) ∣ y ∧
    ¬ (7 : ℤ) ∣ z ∧ ¬ (7 : ℤ) ∣ y + z ∧
    ¬ (7 : ℤ) ∣ v ∧ ¬ (7 : ℤ) ∣ u + 4 * v ∧
    ¬ (7 : ℤ) ∣ seventhPowerSndLeftCubic u v ∧
    ¬ (7 : ℤ) ∣ seventhPowerSndRightCubic u v ∧
    (49 : ℤ) ∣ cyclotomicSevenFst z y - seventhPowerFst u v ∧
    (49 : ℤ) ∣ y * z * (y + z) -
      7 * |v| * |seventhPowerSndLeftCubic u v| *
        |seventhPowerSndRightCubic u v| := by
  norm_num [cyclotomicSevenFst, seventhPowerFst,
    seventhPowerSndLeftCubic, seventhPowerSndRightCubic]

end DkMath.FLT.Seven
