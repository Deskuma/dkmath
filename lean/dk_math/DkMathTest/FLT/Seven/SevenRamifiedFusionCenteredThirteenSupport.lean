/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport"
set_option exponentiation.threshold 400

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {D q : ℕ} (h : ¬ 13 ∣ D) : ¬ 13 ∣ centeredSevenSextic D q :=
  centeredSevenSextic_not_dvd_thirteen h
example {r s : ℕ} (hr : ¬ 13 ∣ r) (hs : 13 ∣ s) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49 :=
  centeredSevenSextic_no_image_of_thirteen_support hr hs
example {M r : ℕ} (hr : ¬ 13 ∣ r) (hs : 13 ∣ M / r) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  nestedAllocation_excluded_of_thirteen_support hr hs

/-- A primitive r3 composite candidate passes prior filters and a mod5 image
match while the complementary13-support obstruction excludes its exact receiver. -/
theorem allocationThree_thirteenSupport_regression :
    ModFortyTwoCheapAllocation (3 * 13 ^ 12) 3 ∧
    SixthPowerAllocationSieve 3 ((3 * 13 ^ 12) / 3) ∧
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27 * 3 ^ 49) 2) (448 * (13 ^ 12) ^ 49) ∧
    ¬ (NestedGNAllocationCondition (3 * 13 ^ 12) 3 ∨
      NestedRHSAllocationCondition (3 * 13 ^ 12) 3) := by
  refine ⟨?_, ⟨13 ^ 2, by decide⟩, by decide,
    nestedAllocation_excluded_of_thirteen_support (by decide) (by decide)⟩
  refine ⟨?_, by decide, by decide, by decide, .inl (by decide)⟩
  exact Nat.mem_divisors.mpr ⟨⟨13 ^ 12, rfl⟩, by positivity⟩

example : (3 * 13 ^ 12 : ℕ) / 3 = 13 ^ 12 ∧
    (13 ^ 2 : ℕ) ^ 6 = 13 ^ 12 := by decide
example : Nat.ModEq 5 (13 ^ 12) 1 ∧ ¬ Nat.ModEq 5 (13 ^ 12) (3 ^ 2) := by decide
example : ((Finset.univ.image (fun q : Fin 13 => centeredSevenSextic 2 q.val % 13)) : Finset ℕ)
    = {1, 4, 5, 10, 12} := by decide

#print axioms DkMath.FLT.Seven.centeredSevenSextic_not_dvd_thirteen
#print axioms DkMath.FLT.Seven.centeredSevenSextic_no_image_of_thirteen_support
#print axioms DkMath.FLT.Seven.nestedAllocation_excluded_of_thirteen_support
#print axioms DkMathTest.FLT.Seven.allocationThree_thirteenSupport_regression
end DkMathTest.FLT.Seven
