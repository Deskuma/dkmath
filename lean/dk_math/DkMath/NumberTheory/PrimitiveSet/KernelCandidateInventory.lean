/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.KernelCandidateInventory"

namespace DkMath.NumberTheory.PrimitiveSet

/--
The canonical exponent-slot kernel is the current equality-route reference
model.
-/
theorem kernelInventory_canonicalExponentSlotKernel_ready :
    CanonicalExponentSlotIndex canonicalExponentSlotKernel :=
  canonicalExponentSlotKernel_canonicalExponentSlotIndex

/-- At state `2`, the sample-ten kernel has no labels. -/
theorem sampleTenPrimePowerDivisorTransitionKernel_index_two_empty :
    sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index 2 = ∅ := by
  simp [sampleTenPrimePowerDivisorTransitionKernel, sampleTenDivisorTransitionKernel]

/-- The canonical exponent-slot index at state `2` contains the label `2`. -/
theorem two_mem_canonicalExponentSlotLabels_two :
    2 ∈ canonicalExponentSlotLabels 2 := by
  rw [canonicalExponentSlotLabels_mem_iff]
  exact ⟨2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/--
The state-`10` sample kernel is a local sanity-check kernel, not a global
canonical exponent-slot index.
-/
theorem sampleTenPrimePowerDivisorTransitionKernel_not_canonicalExponentSlotIndex :
    ¬ CanonicalExponentSlotIndex sampleTenPrimePowerDivisorTransitionKernel := by
  intro H
  have hnot :
      2 ∉ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index 2 := by
    simp [sampleTenPrimePowerDivisorTransitionKernel_index_two_empty]
  rw [H.index_eq 2] at hnot
  exact hnot two_mem_canonicalExponentSlotLabels_two

/--
Replacing the sample-ten weights keeps the same local index, so the toy-weighted
sample is also not a global canonical exponent-slot index.
-/
theorem sampleTenToyWeightKernel_not_canonicalExponentSlotIndex :
    ¬ CanonicalExponentSlotIndex sampleTenToyWeightKernel := by
  intro H
  have hnot :
      2 ∉ sampleTenToyWeightKernel.toDivisorTransitionKernel.index 2 := by
    simp [sampleTenToyWeightKernel, sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel]
  rw [H.index_eq 2] at hnot
  exact hnot two_mem_canonicalExponentSlotLabels_two

end DkMath.NumberTheory.PrimitiveSet
