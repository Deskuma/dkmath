/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage"

/-! A fixed-gap modular image obstruction and an unbounded family of cheap
candidates whose divisor-one exact receivers fail. -/

namespace DkMath.FLT.Seven

/-- The actual fixed-gap sextic has only residues one, two or four modulo five. -/
theorem centeredSevenSextic_fixedGap_mod_five_image (q : ℕ) :
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 1 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 2 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 4 := by
  suffices h : (centeredSevenSextic (7 ^ 27) q : ZMod 5) = 1 ∨
      (centeredSevenSextic (7 ^ 27) q : ZMod 5) = 2 ∨
      (centeredSevenSextic (7 ^ 27) q : ZMod 5) = 4 by
    rcases h with h | h | h
    · exact .inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
    · exact .inr (.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h))
    · exact .inr (.inr ((ZMod.natCast_eq_natCast_iff _ _ _).mp h))
  have hq := Nat.mod_lt q (by decide : 0 < 5)
  simp only [centeredSevenSextic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← ZMod.natCast_mod q 5]
  interval_cases q % 5 <;> decide

/-- Forty-ninth powers preserve residues modulo five, including zero. -/
private theorem centeredTarget_mod_five (s : ℕ) :
    Nat.ModEq 5 (448 * s ^ 49) (3 * s) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [← ZMod.natCast_mod s 5]
  have hs := Nat.mod_lt s (by decide : 0 < 5)
  interval_cases s % 5 <;> decide

/-- Residue one complementary factors have target residue three, outside the image. -/
theorem centeredSevenSextic_fixedGap_no_image_mod_five {s : ℕ} (hs : Nat.ModEq 5 s 1) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * s ^ 49 := by
  rintro ⟨q, heq⟩
  have ht : Nat.ModEq 5 (448 * s ^ 49) 3 := by
    simpa only [one_pow, mul_one] using (centeredTarget_mod_five s).trans (hs.mul_left 3)
  rcases centeredSevenSextic_fixedGap_mod_five_image q with h | h | h
  all_goals
    rw [heq] at h
    have hbad := ht.symm.trans h
    norm_num [Nat.ModEq] at hbad

/-- The exact receiver at divisor one is excluded by the modular image obstruction. -/
theorem nestedAllocation_one_excluded_of_mod_five {M : ℕ} (hM5 : Nat.ModEq 5 M 1) :
    ¬ (NestedGNAllocationCondition M 1 ∨ NestedRHSAllocationCondition M 1) := by
  intro h
  rcases (nestedAllocation_iff_centered M 1).mp h with ⟨q, hq⟩
  apply centeredSevenSextic_fixedGap_no_image_mod_five hM5
  refine ⟨q, ?_⟩
  simpa only [one_pow, mul_one, Nat.div_one, ← mul_assoc,
    show (64 : ℕ) * 7 = 448 by decide] using hq.2.1

/-- Every family member passes cheap and sixth-power filters but has no divisor-one receiver. -/
theorem mod42Cheap_modFive_family (k : ℕ) :
    ModFortyTwoCheapAllocation (631 + 210 * k) 1 ∧
    SixthPowerAllocationSieve 1 ((631 + 210 * k) / 1) ∧
    ¬ (NestedGNAllocationCondition (631 + 210 * k) 1 ∨
      NestedRHSAllocationCondition (631 + 210 * k) 1) := by
  have hident : 631 + 210 * k = 631 + 42 * (5 * k) := by omega
  refine ⟨?_, ?_, nestedAllocation_one_excluded_of_mod_five ?_⟩
  · rw [hident]
    exact mod42Cheap_family (5 * k)
  · rw [hident]
    exact mod42Cheap_family_sixthPower (5 * k)
  · unfold Nat.ModEq
    omega

end DkMath.FLT.Seven
