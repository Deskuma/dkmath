/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion
import DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation
import DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {s : ℕ} (h42 : Nat.ModEq 42 s 1) (h5 : Nat.ModEq 5 s 4)
    (hb : 2 * s < 7 ^ 3 * 5 ^ 7) : ¬ SixthPowerSievedNestedCondition (2 * s) :=
  sixthPowerSieved_two_times_complement_excluded h42 h5 hb
example {k : ℕ} (h : k ≤ 63799) :
    ¬ SixthPowerSievedNestedCondition (2 * (589 + 210 * k)) :=
  sixthPowerSieved_bounded_mixed_family_excluded h

example (k : ℕ) : 2 * (589 + 210 * k) < 7 ^ 3 * 5 ^ 7 ↔ k ≤ 63799 := by
  norm_num
  omega
example : 2 * (589 + 210 * 63799) = (26796758 : ℕ) ∧
    26796758 < 7 ^ 3 * 5 ^ 7 ∧ 7 ^ 3 * 5 ^ 7 = (26796875 : ℕ) := by decide
example : ¬ 2 * (589 + 210 * 63800) < 7 ^ 3 * 5 ^ 7 := by decide
example : 2 * (589 + 210 * 22982) = (9653618 : ℕ) := by decide
example : ¬ SixthPowerSievedNestedCondition (2 * (589 + 210 * 22982)) :=
  sixthPowerSieved_bounded_mixed_family_excluded (by decide)

private theorem mixedCore_injective : Function.Injective (fun k : ℕ => 2 * (589 + 210 * k)) := by
  intro a b h
  change 2 * (589 + 210 * a) = 2 * (589 + 210 * b) at h
  omega

example : ((Finset.range 63800).image (fun k : ℕ => 2 * (589 + 210 * k))).card = 63800 := by
  simpa only [Finset.card_range] using
    Finset.card_image_of_injective (Finset.range 63800) mixedCore_injective

-- Reuse prior same-divisor evidence at the actual k=22982 member.
example : HasModFortyTwoCheapAllocation 9653618 ∧ ¬ SixthPowerSievedNestedCondition 9653618 :=
  ⟨⟨2, allocationTwo_modFive_regression.1⟩, sixthPowerSievedNestedCondition_9653618_excluded⟩

#print axioms DkMath.FLT.Seven.sixthPowerSieved_two_times_complement_excluded
#print axioms DkMath.FLT.Seven.sixthPowerSieved_bounded_mixed_family_excluded
end DkMathTest.FLT.Seven
