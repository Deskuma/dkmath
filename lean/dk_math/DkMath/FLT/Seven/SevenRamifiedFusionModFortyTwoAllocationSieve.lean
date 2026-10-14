/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues
import DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve"

/-! Divisor-aware necessary congruences for the two existing nested receivers.
No allocation existence, emptiness, or FLT7 closure is asserted. -/

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

/-- Forty-ninth powers preserve every residue modulo six, including nonunits. -/
private theorem fortyNinth_power_mod_six (s : ℕ) : Nat.ModEq 6 (s ^ 49) s := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [← ZMod.natCast_mod s 6]
  have hs := Nat.mod_lt s (by decide : 0 < 6)
  interval_cases s % 6 <;> decide

/-- Recover the complementary factor from its exact residual residue. -/
private theorem complementary_mod_six {s : ℕ}
    (h : Nat.ModEq 6 (7 * s ^ 49) 1) : Nat.ModEq 6 s 1 := by
  have hreduce : Nat.ModEq 6 (7 * s ^ 49) s := by
    simpa only [one_mul] using
      (show Nat.ModEq 6 7 1 by decide).mul (fortyNinth_power_mod_six s)
  exact hreduce.symm.trans h

/-- Both exact receivers force the complementary factor to be one modulo six.
The divisor guard supplies the GN branch's missing coprimality provenance. -/
theorem nestedAllocation_mod_six {M r : ℕ} (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 6 (M / r) 1 := by
  apply complementary_mod_six
  rcases h with ⟨u, _, hcop, hGN⟩ | ⟨u, _, huD, hcop, hAlt⟩
  · have hu7 : Nat.Coprime u 7 := hcop.of_dvd_right (dvd_mul_right 7 M)
    have hur : Nat.Coprime u r :=
      hcop.of_dvd_right (hdiv.trans (dvd_mul_left M 7))
    have hDu : Nat.Coprime (7 ^ 27 * r ^ 49) u :=
      ((hu7.pow_right 27).mul_right (hur.pow_right 49)).symm
    simpa only [hGN] using GN_seven_mod_six_of_coprime hDu
  · have hpair : Nat.Coprime u (7 ^ 27 * r ^ 49 - u) :=
      (Nat.coprime_sub_self_right huD.le).mpr hcop
    simpa only [hAlt] using alternatingCyclotomicSeven_mod_six_of_coprime hpair

/-- Combine the divisor-aware modulo-six constraint with the existing modulo-seven sieve. -/
theorem nestedAllocation_mod_fortyTwo {M r : ℕ} (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 42 (M / r) 1 := by
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 6 7)).mp
    ⟨nestedAllocation_mod_six hdiv h, nestedAllocation_residue_sieve h⟩

/-- A failed necessary residue excludes both receivers at this divisor allocation. -/
theorem nestedAllocation_excluded_of_mod_fortyTwo {M r : ℕ} (hdiv : r ∣ M)
    (hbad : ¬ Nat.ModEq 42 (M / r) 1) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  fun h => hbad (nestedAllocation_mod_fortyTwo hdiv h)

end DkMath.FLT.Seven
