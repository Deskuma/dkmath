/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullChannelEquality

#print "file: DkMath.NumberTheory.PrimitiveSet.FullExponentSlot"

namespace DkMath.NumberTheory.PrimitiveSet

/--
Exact base-prime multiplicity against the prime factorization of `n`.

This is the equality counterpart of `NatBaseMultiplicityBudgetOn`: every prime
fiber has exactly as many selected labels as the exponent slot count in `n`.
-/
def NatBaseMultiplicityCompleteOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → NatBaseMultiplicityOn I pOf p = n.factorization p

/-- Exact multiplicity immediately supplies the earlier multiplicity budget. -/
theorem natBaseMultiplicityBudgetOn_of_complete
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hcomplete : NatBaseMultiplicityCompleteOn I pOf n) :
    NatBaseMultiplicityBudgetOn I pOf n := by
  intro p hp
  exact le_of_eq (hcomplete p hp)

/--
The finite full-channel set is extensionally the set of prime-power exponent
slots of `n`.

This is a specification interface only.  It avoids committing to a concrete
`Finset` construction before the equality route chooses whether to work on
labels `q` or on explicit `(p,k)` slots.
-/
structure FullExponentSlotChannelSet
    {T : PrimePowerDivisorTransitionKernel}
    (C : FullPrimePowerChannelSet T) : Prop where
  mem_iff :
    ∀ n q,
      q ∈ C.channels n ↔
        ∃ p k,
          Nat.Prime p ∧
          1 ≤ k ∧
          k ≤ n.factorization p ∧
          q = p ^ k

namespace FullExponentSlotChannelSet

theorem mem_channels_of_slot
    {T : PrimePowerDivisorTransitionKernel}
    {C : FullPrimePowerChannelSet T}
    (H : FullExponentSlotChannelSet C)
    {n q p k : ℕ}
    (hp : Nat.Prime p)
    (hk_pos : 1 ≤ k)
    (hk_le : k ≤ n.factorization p)
    (hq : q = p ^ k) :
    q ∈ C.channels n :=
  (H.mem_iff n q).mpr ⟨p, k, hp, hk_pos, hk_le, hq⟩

theorem exists_slot_of_mem_channels
    {T : PrimePowerDivisorTransitionKernel}
    {C : FullPrimePowerChannelSet T}
    (H : FullExponentSlotChannelSet C)
    {n q : ℕ}
    (hq : q ∈ C.channels n) :
    ∃ p k,
      Nat.Prime p ∧
      1 ≤ k ∧
      k ≤ n.factorization p ∧
      q = p ^ k :=
  (H.mem_iff n q).mp hq

end FullExponentSlotChannelSet

/--
The witness-provider reader fills every base-prime exponent slot.

For each state `s` and prime `p`, the number of full-channel labels whose
witness base is `p` is exactly `s.1.factorization p`.  This is the equality-side
counterpart of the existing R027-style `≤` multiplicity bound.
-/
structure FullExponentSlotCoverage
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) : Prop where
  baseMultiplicity_complete :
    ∀ s : LogCapacityState,
      NatBaseMultiplicityCompleteOn
        (C.channels s.1)
        (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))
        s.1

namespace PrimePowerWitnessProvider

/-- Full exponent-slot coverage gives exact base-prime multiplicities. -/
theorem fullExponentSlotCoverage_baseMultiplicity_complete
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    NatBaseMultiplicityCompleteOn
      (C.channels s.1)
      (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))
      s.1 :=
  H.baseMultiplicity_complete s

/--
Full exponent-slot coverage strengthens the existing selected-channel
multiplicity budget at every state.
-/
theorem fullExponentSlotCoverage_baseMultiplicity_budget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    NatBaseMultiplicityBudgetOn
      (C.channels s.1)
      (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))
      s.1 :=
  natBaseMultiplicityBudgetOn_of_complete
    (C.channels s.1)
    (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))
    s.1
    (W.fullExponentSlotCoverage_baseMultiplicity_complete C H s)

/-- Fiber-card form of full exponent-slot coverage. -/
theorem fullExponentSlotCoverage_card_filter_eq_factorization
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState)
    {p : ℕ}
    (hp : Nat.Prime p) :
    ((C.channels s.1).filter
        (fun q =>
          W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1) q = p)).card =
      s.1.factorization p :=
  H.baseMultiplicity_complete s p hp

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
