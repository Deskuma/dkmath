/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.NumberTheory.Primitive.CrossPeriod"

/-! Neutral product-period collision arithmetic extracted from PacketCross. -/

namespace DkMath.NumberTheory.Primitive

/-- Two coprime directions meeting the same ordered pair of waves divide its offset gap. -/
theorem crossPeriod_mul_dvd_diff {a d p q r s : ℕ}
    (hpq : Nat.Coprime p q) (hpr : p ∣ a + r) (hps : p ∣ a + s)
    (hqr : q ∣ a + (d + r)) (hqs : q ∣ a + (d + s)) :
    p * q ∣ s - r := by
  have hp : p ∣ s - r := by
    simpa only [Nat.add_sub_add_left] using Nat.dvd_sub hps hpr
  have hq : q ∣ s - r := by
    simpa only [Nat.add_sub_add_left] using Nat.dvd_sub hqs hqr
  exact hpq.mul_dvd_of_dvd_of_dvd hp hq

end DkMath.NumberTheory.Primitive
