/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example (q : ℕ) : Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 1 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 2 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 4 :=
  centeredSevenSextic_fixedGap_mod_five_image q

-- Each of the three residues is attained; this is the exact modular image.
example : Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) 0) 4 := by decide
example : Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) 1) 2 := by decide
example : Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) 2) 1 := by decide
example : Nat.ModEq 5 (7 ^ 27) 3 := by decide

example {s : ℕ} (hs : Nat.ModEq 5 s 1) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * s ^ 49 :=
  centeredSevenSextic_fixedGap_no_image_mod_five hs
example {M : ℕ} (h : Nat.ModEq 5 M 1) :
    ¬ (NestedGNAllocationCondition M 1 ∨ NestedRHSAllocationCondition M 1) :=
  nestedAllocation_one_excluded_of_mod_five h

example (k : ℕ) : Nat.ModEq 5 (631 + 210 * k) 1 ∧
    Nat.ModEq 42 (631 + 210 * k) 1 := by
  constructor <;> unfold Nat.ModEq <;> omega
example (k : ℕ) : ModFortyTwoCheapAllocation (631 + 210 * k) 1 ∧
    SixthPowerAllocationSieve 1 ((631 + 210 * k) / 1) ∧
    ¬ (NestedGNAllocationCondition (631 + 210 * k) 1 ∨
      NestedRHSAllocationCondition (631 + 210 * k) 1) := mod42Cheap_modFive_family k
example (k : ℕ) : HasModFortyTwoCheapAllocation (631 + 210 * k) :=
  ⟨1, (mod42Cheap_modFive_family k).1⟩
example : Function.Injective (fun k : ℕ => 631 + 210 * k) := by
  intro a b h
  change 631 + 210 * a = 631 + 210 * b at h
  omega
example (B : ℕ) : ∃ k : ℕ, B < 631 + 210 * k ∧
    ModFortyTwoCheapAllocation (631 + 210 * k) 1 ∧
    SixthPowerAllocationSieve 1 ((631 + 210 * k) / 1) ∧
    ¬ (NestedGNAllocationCondition (631 + 210 * k) 1 ∨
      NestedRHSAllocationCondition (631 + 210 * k) 1) :=
  ⟨B, by omega, mod42Cheap_modFive_family B⟩

-- Modular matching at 589 is compatible with the independent adjacent-gap exclusion.
example : Nat.ModEq 5 589 4 ∧ Nat.ModEq 5 (448 * 589 ^ 49) 2 := by decide
example : Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) 1) (448 * 589 ^ 49) ∧
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * 589 ^ 49 :=
  ⟨by decide, centeredSevenSextic_589_no_image⟩

#print axioms DkMath.FLT.Seven.centeredSevenSextic_fixedGap_mod_five_image
#print axioms DkMath.FLT.Seven.centeredSevenSextic_fixedGap_no_image_mod_five
#print axioms DkMath.FLT.Seven.nestedAllocation_one_excluded_of_mod_five
#print axioms DkMath.FLT.Seven.mod42Cheap_modFive_family

end DkMathTest.FLT.Seven
