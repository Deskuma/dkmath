/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation"

-- Allow literal 1^343 in the fixed-allocation size guards to normalize.
set_option exponentiation.threshold 400

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven

-- The fixed-allocation filter uses only decidable arithmetic conditions.
example (M r : ℕ) : Decidable (ModFortyTwoCheapAllocation M r) := by
  unfold ModFortyTwoCheapAllocation
  infer_instance

-- The new numeric filter implies the older numeric guards (sixth powers stay separate).
example {M r : ℕ} (h : ModFortyTwoCheapAllocation M r) :
    r ∈ M.divisors ∧ Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
      Nat.ModEq 7 (M / r) 1 ∧
      (7 ^ 161 * r ^ 343 < M ^ 49 ∨
        (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49)) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.of_dvd (by decide : 7 ∣ 42), h.2.2.2.2⟩

-- These are necessary-only guards, not SixthPowerSievedNestedCondition 554.
theorem candidate554_old_guards : 1 ∈ (554 : ℕ).divisors ∧ Nat.Coprime 1 (554 / 1) ∧
    7 ^ 3 * 1 ^ 7 < 554 ∧ Nat.ModEq 7 (554 / 1) 1 ∧
    (554 ^ 49 < 7 ^ 161 * 1 ^ 343 ∧ 7 ^ 161 * 1 ^ 343 ≤ 64 * 554 ^ 49) ∧
    SixthPowerAllocationSieve 1 (554 / 1) := by
  refine ⟨?_, by decide, by decide, by decide, ⟨by decide, by decide⟩,
    sixthPowerAllocationSieve_mod_one _⟩
  norm_num [Nat.mem_divisors]

theorem candidate554_rejected : ¬ ModFortyTwoCheapAllocation 554 1 := by
  intro h
  exact (by decide : ¬ Nat.ModEq 42 (554 / 1) 1) h.2.2.2.1

-- A passing arithmetic candidate supplies no exact endpoint witness.
theorem candidate589_passes : ModFortyTwoCheapAllocation 589 1 := by
  refine ⟨?_, by decide, by decide, by decide, .inr ⟨by decide, by decide⟩⟩
  norm_num [Nat.mem_divisors]


example (M : ℕ) (h : SixthPowerSievedNestedCondition M) :
    HasModFortyTwoCheapAllocation M := sixthPowerSieved_implies_mod42Cheap M h

open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

example (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    HasModFortyTwoCheapAllocation (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_implies_mod42Cheap p h

example : HasModFortyTwoCheapAllocation 589 := ⟨1, candidate589_passes⟩

-- Pointwise discrimination does not claim absence of other divisors.
example : ¬ (∀ M r : ℕ,
    (r ∈ M.divisors ∧ Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
      Nat.ModEq 7 (M / r) 1 ∧
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49) ∧
      SixthPowerAllocationSieve r (M / r)) → ModFortyTwoCheapAllocation M r) := by
  intro h
  exact candidate554_rejected (h 554 1 candidate554_old_guards)

#print axioms DkMath.FLT.Seven.sixthPowerSieved_implies_mod42Cheap
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_implies_mod42Cheap
#print axioms DkMathTest.FLT.Seven.candidate554_old_guards
#print axioms DkMathTest.FLT.Seven.candidate554_rejected
#print axioms DkMathTest.FLT.Seven.candidate589_passes

end DkMathTest.FLT.Seven
