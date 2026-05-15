/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel

#print "file: DkMath.NumberTheory.PrimitiveSet.FullChannelSet"

namespace DkMath.NumberTheory.PrimitiveSet

/--
A chosen channel set that is extensionally the full prime-power transition index.

This is an interface layer only.  It does not assert the analytic equality
`Σ log p = log n`; it records the finite full-channel choice needed before that
equality route can be stated cleanly.
-/
structure FullPrimePowerChannelSet
    (T : PrimePowerDivisorTransitionKernel) where
  channels : ℕ → Finset ℕ
  subset_index :
    ∀ n q, q ∈ channels n → q ∈ T.toDivisorTransitionKernel.index n
  full :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → q ∈ channels n

namespace FullPrimePowerChannelSet

/-- The canonical full-channel choice is the transition kernel index itself. -/
def canonical
    (T : PrimePowerDivisorTransitionKernel) :
    FullPrimePowerChannelSet T where
  channels := T.toDivisorTransitionKernel.index
  subset_index := by
    intro n q hq
    exact hq
  full := by
    intro n q hq
    exact hq

@[simp] theorem canonical_channels
    (T : PrimePowerDivisorTransitionKernel) :
    (canonical T).channels = T.toDivisorTransitionKernel.index :=
  rfl

/-- A full channel set has exactly the same members as the transition index. -/
theorem mem_channels_iff
    {T : PrimePowerDivisorTransitionKernel}
    (C : FullPrimePowerChannelSet T)
    (n q : ℕ) :
    q ∈ C.channels n ↔ q ∈ T.toDivisorTransitionKernel.index n :=
  ⟨C.subset_index n q, C.full n q⟩

/-- A full channel set is extensionally equal to the transition index. -/
theorem channels_eq_index
    {T : PrimePowerDivisorTransitionKernel}
    (C : FullPrimePowerChannelSet T)
    (n : ℕ) :
    C.channels n = T.toDivisorTransitionKernel.index n := by
  ext q
  exact C.mem_channels_iff n q

end FullPrimePowerChannelSet

end DkMath.NumberTheory.PrimitiveSet
