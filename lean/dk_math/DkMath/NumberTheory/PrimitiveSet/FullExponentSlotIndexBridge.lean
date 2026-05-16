/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical

#print "file: DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge"

namespace DkMath.NumberTheory.PrimitiveSet

/--
An arbitrary prime-power divisor transition kernel has the canonical
exponent-slot index.

This is the comparison interface between an external `T.index n` and the
concrete reference model `canonicalExponentSlotLabels n`.
-/
structure CanonicalExponentSlotIndex
    (T : PrimePowerDivisorTransitionKernel) : Prop where
  index_eq :
    ∀ n, T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n

namespace CanonicalExponentSlotIndex

/-- Membership in a canonical exponent-slot index, expanded as exponent slots. -/
theorem mem_iff
    {T : PrimePowerDivisorTransitionKernel}
    (H : CanonicalExponentSlotIndex T)
    (n q : ℕ) :
    q ∈ T.toDivisorTransitionKernel.index n ↔
      ∃ p k, Nat.Prime p ∧ 1 ≤ k ∧ k ≤ n.factorization p ∧ q = p ^ k := by
  rw [H.index_eq n]
  exact canonicalExponentSlotLabels_mem_iff

end CanonicalExponentSlotIndex

/-- The concrete canonical exponent-slot kernel has the canonical exponent-slot index. -/
theorem canonicalExponentSlotKernel_canonicalExponentSlotIndex :
    CanonicalExponentSlotIndex canonicalExponentSlotKernel := by
  constructor
  intro _n
  rfl

/--
If a full kernel's index is the canonical exponent-slot label set, then its
canonical full-channel choice is a `FullExponentSlotChannelSet`.
-/
theorem fullExponentSlotChannelSet_of_canonicalExponentSlotIndex
    {T : PrimePowerDivisorTransitionKernel}
    (H : CanonicalExponentSlotIndex T) :
    FullExponentSlotChannelSet (FullPrimePowerChannelSet.canonical T) := by
  constructor
  intro n q
  exact H.mem_iff n q

namespace PrimePowerWitnessProvider

/--
A witness provider over a kernel with canonical exponent-slot index satisfies
full-channel log-cost completeness.
-/
theorem fullChannelLogCostComplete_of_canonicalExponentSlotIndex
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (H : CanonicalExponentSlotIndex T) :
    FullChannelLogCostComplete W (FullPrimePowerChannelSet.canonical T) :=
  W.fullChannelLogCostComplete_of_fullExponentSlotChannelSet
    (FullPrimePowerChannelSet.canonical T)
    (fullExponentSlotChannelSet_of_canonicalExponentSlotIndex H)

/--
Any witness provider over a kernel whose index is the canonical exponent-slot
label set has a full global log-capacity Markov shadow.
-/
noncomputable def fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (H : CanonicalExponentSlotIndex T) :
    MarkovShadow LogCapacityState ℕ :=
  W.fullGlobalLogCapacityMarkovShadow
    (FullPrimePowerChannelSet.canonical T)
    (W.fullChannelLogCostComplete_of_canonicalExponentSlotIndex H)

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
