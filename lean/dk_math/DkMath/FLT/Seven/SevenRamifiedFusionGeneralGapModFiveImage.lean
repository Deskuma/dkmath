/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage"

/-! Divisor-dependent modular obstruction for the actual centered sextic.
The divisor is retained in the gap and in the exact receiver transport. -/

namespace DkMath.FLT.Seven

/-- A unit divisor cannot realize the target when the complementary residue is its square. -/
theorem centeredSevenSextic_generalGap_no_image_mod_five {r s : ℕ}
    (hr5 : ¬ 5 ∣ r) (hs5 : Nat.ModEq 5 s (r ^ 2)) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49 := by
  rintro ⟨q, heq⟩
  have hs : (s : ZMod 5) = (r : ZMod 5) ^ 2 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hs5
  have he := congrArg (fun n : ℕ => (n : ZMod 5)) heq
  simp only [centeredSevenSextic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] at he
  rw [hs, ← ZMod.natCast_mod r 5, ← ZMod.natCast_mod q 5] at he
  have hrmod : r % 5 ≠ 0 := fun h => hr5 (Nat.dvd_of_mod_eq_zero h)
  have hr := Nat.mod_lt r (by decide : 0 < 5)
  have hq := Nat.mod_lt q (by decide : 0 < 5)
  interval_cases r % 5 <;> interval_cases q % 5 <;>
    norm_num at hrmod <;> revert he <;> decide

/-- Transport the general-gap obstruction to the same chosen exact allocation. -/
theorem nestedAllocation_excluded_of_mod_five_square {M r : ℕ}
    (hr5 : ¬ 5 ∣ r) (hs5 : Nat.ModEq 5 (M / r) (r ^ 2)) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) := by
  intro h
  rcases (nestedAllocation_iff_centered M r).mp h with ⟨q, hq⟩
  apply centeredSevenSextic_generalGap_no_image_mod_five hr5 hs5
  refine ⟨q, ?_⟩
  simpa only [← mul_assoc, show (64 : ℕ) * 7 = 448 by decide] using hq.2.1

end DkMath.FLT.Seven
