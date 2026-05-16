/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum

#print "file: DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

namespace PrimePowerWitnessProvider

/--
If an indexed label is extensionally `p^k`, then the witness-provider base
reader must return `p`.

The witness provider may choose a witness internally, but prime divisibility of
prime powers forces the base prime to be unique.
-/
theorem basePrimeOf_eq_of_prime_pow_mem
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    {q p k : ℕ}
    (hqI : q ∈ I)
    (hp : Nat.Prime p)
    (hq : q = p ^ k) :
    W.basePrimeOf n I hI q = p := by
  unfold basePrimeOf
  rw [dif_pos hqI]
  let L := W.label n q (hI q hqI)
  have hLdvd_q : L.p ∣ q := by
    have hLdvd_Lq : L.p ∣ L.q := by
      rw [L.eq_pow]
      exact dvd_pow_self _ (Nat.ne_of_gt L.k_pos)
    simpa [L, W.label_q n q (hI q hqI)] using hLdvd_Lq
  have hLdvd_pow : L.p ∣ p ^ k := by
    simpa [hq] using hLdvd_q
  exact Nat.prime_eq_prime_of_dvd_pow L.prime hp hLdvd_pow

/--
A full channel set that is extensionally the exponent-slot set supplies full
exponent-slot coverage.

The upper bound is the existing selected-channel valuation budget.  The lower
bound sends every slot `k = 1, ..., v_p(n)` to the distinct label `p^k`.
-/
theorem fullExponentSlotCoverage_of_fullExponentSlotChannelSet
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (Hslot : FullExponentSlotChannelSet C) :
    FullExponentSlotCoverage W C := by
  constructor
  intro s p hp
  let I := C.channels s.1
  let pOf := W.basePrimeOf s.1 I (C.subset_index s.1)
  apply le_antisymm
  · exact W.basePrimeOf_card_filter_le_factorization s.1 I (C.subset_index s.1)
      (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one s.2)) p
  · let E := Finset.Icc 1 (s.1.factorization p)
    have hcard_img : E.card = (E.image fun k => p ^ k).card := by
      symm
      exact Finset.card_image_of_injective _ (Nat.pow_right_injective hp.two_le)
    have himage_sub : (E.image fun k => p ^ k) ⊆ I.filter (fun q => pOf q = p) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨k, hkE, rfl⟩
      have hk_bounds := Finset.mem_Icc.mp hkE
      have hqI : p ^ k ∈ I := by
        exact Hslot.mem_channels_of_slot hp hk_bounds.1 hk_bounds.2 rfl
      have hbase : pOf (p ^ k) = p := by
        exact W.basePrimeOf_eq_of_prime_pow_mem s.1 I (C.subset_index s.1) hqI hp rfl
      exact Finset.mem_filter.mpr ⟨hqI, hbase⟩
    calc
      s.1.factorization p = E.card := by simp [E, Nat.card_Icc]
      _ = (E.image fun k => p ^ k).card := hcard_img
      _ ≤ (I.filter fun q => pOf q = p).card := Finset.card_le_card himage_sub
      _ = NatBaseMultiplicityOn I pOf p := by rfl

/--
Exponent-slot channel extensionality supplies the full-channel log-cost
completeness interface.
-/
theorem fullChannelLogCostComplete_of_fullExponentSlotChannelSet
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (Hslot : FullExponentSlotChannelSet C) :
    FullChannelLogCostComplete W C :=
  W.fullChannelLogCostComplete_of_fullExponentSlotCoverage C
    (W.fullExponentSlotCoverage_of_fullExponentSlotChannelSet C Hslot)

/--
If the full channel set is exactly the exponent-slot set, the full global
log-capacity shadow is Markov.
-/
noncomputable def fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (Hslot : FullExponentSlotChannelSet C) :
    MarkovShadow LogCapacityState ℕ :=
  W.fullGlobalLogCapacityMarkovShadow C
    (W.fullChannelLogCostComplete_of_fullExponentSlotChannelSet C Hslot)

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
