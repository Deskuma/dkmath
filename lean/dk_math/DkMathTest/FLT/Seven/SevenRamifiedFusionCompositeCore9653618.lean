/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation
import DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionCompositeCore9653618"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {r : ℕ} (hm : r ∈ (9653618 : ℕ).divisors)
    (hs : 7 ^ 3 * r ^ 7 < 9653618) : r = 1 ∨ r = 2 :=
  eligible_divisor_9653618_eq_one_or_two hm hs
example : ModFortyTwoCheapAllocation 9653618 2 ∧
    SixthPowerAllocationSieve 2 (9653618 / 2) ∧
    ¬ (NestedGNAllocationCondition 9653618 2 ∨ NestedRHSAllocationCondition 9653618 2) :=
  ⟨allocationTwo_modFive_regression.1, allocationTwo_modFive_regression.2.1,
    allocationTwo_modFive_regression.2.2.1⟩
example : ¬ (NestedGNAllocationCondition 9653618 1 ∨ NestedRHSAllocationCondition 9653618 1) :=
  nestedAllocation_excluded_of_mod_fortyTwo (by decide) (by decide)
example : ¬ SixthPowerSievedNestedCondition 9653618 :=
  sixthPowerSievedNestedCondition_9653618_excluded
example : HasModFortyTwoCheapAllocation 9653618 ∧ ¬ SixthPowerSievedNestedCondition 9653618 :=
  ⟨⟨2, allocationTwo_modFive_regression.1⟩, sixthPowerSievedNestedCondition_9653618_excluded⟩
example : (9653618 : ℕ) % 42 = 2 ∧ ¬ 3 ∣ (9653618 : ℕ) ∧ ¬ 4 ∣ (9653618 : ℕ) := by decide

open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport
example (p : RamifiedSignedRootRoutingPacket) (h : internalDepthFourSeventhCore p = 9653618) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  no_reconstruction_of_core_eq_9653618 p h

#print axioms DkMath.FLT.Seven.eligible_divisor_9653618_eq_one_or_two
#print axioms DkMath.FLT.Seven.sixthPowerSievedNestedCondition_9653618_excluded
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_9653618
end DkMathTest.FLT.Seven
