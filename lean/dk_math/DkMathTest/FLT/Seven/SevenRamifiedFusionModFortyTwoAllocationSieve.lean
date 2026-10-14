/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven

-- Proof-level applications preserve the visible divisor guard.
example {M r : ℕ} (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 6 (M / r) 1 := nestedAllocation_mod_six hdiv h

example {M r : ℕ} (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 42 (M / r) 1 := nestedAllocation_mod_fortyTwo hdiv h

example {M r : ℕ} (hdiv : r ∣ M) (hbad : ¬ Nat.ModEq 42 (M / r) 1) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  nestedAllocation_excluded_of_mod_fortyTwo hdiv hbad

-- Receiver coprimality alone does not transport to the allocation factor.
-- These statements do NOT claim the full receiver equation holds.
example : Nat.Coprime 2 (7 * 1) ∧ ¬ Nat.Coprime 2 2 ∧ ¬ 2 ∣ 1 := by decide

example : ¬ Nat.Coprime (7 ^ 27 * 2 ^ 49) 2 := by
  have hdiv : 2 ∣ 7 ^ 27 * 2 ^ 49 :=
    dvd_mul_of_dvd_right (dvd_pow_self 2 (by decide : 49 ≠ 0)) _
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) hdiv (dvd_refl 2)

-- Power sanity checks include zero and nonunits; these are not the universal proof.
example : Nat.ModEq 6 (0 ^ 49) 0 := by decide
example : Nat.ModEq 6 (2 ^ 49) 2 := by decide
example : Nat.ModEq 6 (3 ^ 49) 3 := by decide
example : Nat.ModEq 6 (5 ^ 49) 5 := by decide

example {s : ℕ} (h6 : Nat.ModEq 6 s 1) (h7 : Nat.ModEq 7 s 1) :
    Nat.ModEq 42 s 1 :=
  (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 6 7)).mp ⟨h6, h7⟩
example : Nat.ModEq 42 589 1 := by decide
example : Nat.ModEq 7 8 1 ∧ ¬ Nat.ModEq 42 8 1 := by decide

-- A concrete exclusion uses the new consumer, rather than inspecting endpoints.
example : ¬ (NestedGNAllocationCondition 8 1 ∨ NestedRHSAllocationCondition 8 1) :=
  nestedAllocation_excluded_of_mod_fortyTwo (by decide) (by decide)

-- Passing the necessary filter does not supply an allocation witness.
-- This particular surviving residue is excluded by existing size/threshold facts.
example : Nat.ModEq 42 (1 / 1) 1 ∧
    ¬ (NestedGNAllocationCondition 1 1 ∨ NestedRHSAllocationCondition 1 1) := by
  refine ⟨by decide, ?_⟩
  rintro (hGN | hRHS)
  · have hbad := nestedGNAllocation_threshold (by decide : 0 < 1) (by decide) hGN
    norm_num at hbad
  · rcases hRHS with ⟨u, hu, huD, _, hAlt⟩
    have hbad := (nestedAlternatingResidual_coarse_allocation_bound
      (by decide : 0 < 1) hu huD hAlt).2.2
    norm_num at hbad

#print axioms DkMath.FLT.Seven.nestedAllocation_mod_six
#print axioms DkMath.FLT.Seven.nestedAllocation_mod_fortyTwo
#print axioms DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_fortyTwo

end DkMathTest.FLT.Seven
