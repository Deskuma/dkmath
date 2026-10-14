/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage"

-- The r=2 concrete threshold contains a literal exponent 343.
set_option exponentiation.threshold 400

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {r s : ℕ} (hr : ¬ 5 ∣ r) (hs : Nat.ModEq 5 s (r ^ 2)) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49 :=
  centeredSevenSextic_generalGap_no_image_mod_five hr hs
example {M r : ℕ} (hr : ¬ 5 ∣ r) (hs : Nat.ModEq 5 (M / r) (r ^ 2)) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  nestedAllocation_excluded_of_mod_five_square hr hs

/-- The same r=2 allocation survives both prior filters, fails the new exact
receiver test, and does not meet the prior perfect-sixth size hypothesis. -/
theorem allocationTwo_modFive_regression :
    ModFortyTwoCheapAllocation 9653618 2 ∧
    SixthPowerAllocationSieve 2 (9653618 / 2) ∧
    ¬ (NestedGNAllocationCondition 9653618 2 ∨ NestedRHSAllocationCondition 9653618 2) ∧
    ¬ 9 * 2 ^ 2 ≤ (13 : ℕ) := by
  refine ⟨?_, ⟨13, by decide⟩,
    nestedAllocation_excluded_of_mod_five_square (by decide) (by decide), by decide⟩
  refine ⟨?_, by decide, by decide, by decide, .inl (by decide)⟩
  norm_num [Nat.mem_divisors]

example : (13 : ℕ) ^ 6 = 4826809 ∧ 9653618 = 2 * 4826809 := by decide
example : Nat.ModEq 5 (9653618 / 2) (2 ^ 2) ∧ ¬ 5 ∣ (2 : ℕ) := by decide
example : ¬ Nat.ModEq 5 (9653618 / 2) 1 := by decide

-- Exact finite modular image table, checked by Lean rather than Python.
example : ∀ r : Fin 5,
    (Finset.univ.image (fun q : Fin 5 =>
      centeredSevenSextic (7 ^ 27 * (r.val : ℕ) ^ 49) q.val % 5)) =
    (if r.val = 0 then {0, 2, 3} else
      if r.val = 1 ∨ r.val = 4 then {1, 2, 4} else {1, 3, 4}) := by decide

-- Allowed complementary residues from the same exact finite table.
example : ∀ r s : Fin 5,
    (∃ q : Fin 5, Nat.ModEq 5
      (centeredSevenSextic (7 ^ 27 * (r.val : ℕ) ^ 49) q.val)
      (448 * (s.val : ℕ) ^ 49)) ↔
    s.val ∈ (if r.val = 0 then ({0, 1, 4} : Finset ℕ) else
      if r.val = 1 ∨ r.val = 4 then {2, 3, 4} else {1, 2, 3}) := by decide

-- Dropping the unit premise makes the generic natural no-image claim false.
-- This zero-gap model is not a positive-divisor allocation.
example : Nat.ModEq 5 0 (0 ^ 2) ∧
    ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * 0 ^ 49) q = 448 * 0 ^ 49 :=
  ⟨by decide, 0, by decide⟩

#print axioms DkMath.FLT.Seven.centeredSevenSextic_generalGap_no_image_mod_five
#print axioms DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_five_square
#print axioms DkMathTest.FLT.Seven.allocationTwo_modFive_regression

end DkMathTest.FLT.Seven
