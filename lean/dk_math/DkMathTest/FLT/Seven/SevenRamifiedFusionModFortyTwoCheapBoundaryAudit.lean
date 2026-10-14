/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit
import DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven

example : ¬ HasModFortyTwoCheapAllocation 554 := no_mod42Cheap_at_554
example (k : ℕ) : ModFortyTwoCheapAllocation (631 + 42 * k) 1 := mod42Cheap_family k
example (k : ℕ) : HasModFortyTwoCheapAllocation (631 + 42 * k) := mod42Cheap_family_has k
example (k : ℕ) : SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1) :=
  mod42Cheap_family_sixthPower k
example (B : ℕ) : ∃ k : ℕ, B < 631 + 42 * k ∧
    ModFortyTwoCheapAllocation (631 + 42 * k) 1 ∧
    SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1) := mod42Cheap_survivors_unbounded B

-- Distinct indices give distinct cores; this is not a bounded sample list.
example : Function.Injective (fun k : ℕ => 631 + 42 * k) := by
  intro a b h
  change 631 + 42 * a = 631 + 42 * b at h
  omega

example : 7 ^ 161 < (631 : ℕ) ^ 49 := by decide
example : ModFortyTwoCheapAllocation 631 1 := mod42Cheap_family 0
example : ModFortyTwoCheapAllocation 673 1 := mod42Cheap_family 1

-- Reuse the checked gate-003 survivor rather than redoing its integer comparisons.
example : HasModFortyTwoCheapAllocation 589 := ⟨1, candidate589_passes⟩
example : ModFortyTwoCheapAllocation 589 1 ∧ ¬ HasModFortyTwoCheapAllocation 554 :=
  ⟨candidate589_passes, no_mod42Cheap_at_554⟩

open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport
example (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 554) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  no_reconstruction_of_core_eq_554 p hcore

#print axioms DkMath.FLT.Seven.no_mod42Cheap_at_554
#print axioms DkMath.FLT.Seven.mod42Cheap_family
#print axioms DkMath.FLT.Seven.mod42Cheap_family_has
#print axioms DkMath.FLT.Seven.mod42Cheap_family_sixthPower
#print axioms DkMath.FLT.Seven.mod42Cheap_survivors_unbounded
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_554

end DkMathTest.FLT.Seven
