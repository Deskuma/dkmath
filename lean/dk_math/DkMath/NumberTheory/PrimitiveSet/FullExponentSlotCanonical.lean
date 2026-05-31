/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical"

namespace DkMath.NumberTheory.PrimitiveSet

/--
The canonical finite set of exponent-slot labels for `n`.

It contains exactly the labels `p^k` with `p` in the factorization support and
`1 ≤ k ≤ n.factorization p`.
-/
def canonicalExponentSlotLabels (n : ℕ) : Finset ℕ :=
  n.factorization.support.biUnion fun p =>
    (Finset.Icc 1 (n.factorization p)).image fun k => p ^ k

/-- Membership in the canonical exponent-slot label set. -/
theorem canonicalExponentSlotLabels_mem_iff
    {n q : ℕ} :
    q ∈ canonicalExponentSlotLabels n ↔
      ∃ p k, Nat.Prime p ∧ 1 ≤ k ∧ k ≤ n.factorization p ∧ q = p ^ k := by
  classical
  constructor
  · intro hq
    rcases Finset.mem_biUnion.mp hq with ⟨p, hp_support, hpq⟩
    rcases Finset.mem_image.mp hpq with ⟨k, hk, hqpow⟩
    exact ⟨p, k,
      Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp_support),
      (Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2,
      hqpow.symm⟩
  · rintro ⟨p, k, _hp, hk_pos, hk_le, rfl⟩
    have hp_support : p ∈ n.factorization.support := by
      exact Finsupp.mem_support_iff.mpr
        (Nat.ne_of_gt (lt_of_lt_of_le
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hk_pos) hk_le))
    exact Finset.mem_biUnion.mpr
      ⟨p, hp_support,
        Finset.mem_image.mpr
          ⟨k, Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, rfl⟩⟩

/--
The canonical exponent-slot divisor transition kernel.

It is a minimal concrete kernel: labels are exponent slots, next-state is
division by the label, and the rational transition weight is the zero toy
weight because the log-capacity route supplies the real cost separately.
-/
def canonicalExponentSlotDivisorTransitionKernel : DivisorTransitionKernel where
  index := canonicalExponentSlotLabels
  next := fun n q => n / q
  weight := fun _ _ => 0
  weight_nonneg := by
    intro _n _q _hq
    simp
  index_dvd := by
    intro n q hq
    rcases canonicalExponentSlotLabels_mem_iff.mp hq with
      ⟨p, k, hp, _hk_pos, hk_le, rfl⟩
    by_cases hn : n = 0
    · rw [hn]
      exact dvd_zero _
    · exact (hp.pow_dvd_iff_le_factorization hn).mpr hk_le
  next_eq_div := by
    intro _n _q _hq
    rfl

/-- The packaged prime-power kernel carried by the canonical exponent-slot index. -/
def canonicalExponentSlotKernel : PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel := canonicalExponentSlotDivisorTransitionKernel
  primePowerIndexed := by
    intro n q hq
    rcases canonicalExponentSlotLabels_mem_iff.mp hq with
      ⟨p, k, hp, hk_pos, _hk_le, hqpow⟩
    exact ⟨p, k, hp, Nat.lt_of_lt_of_le Nat.zero_lt_one hk_pos, hqpow⟩

/-- The canonical index has a prime-power label whose underlying label is `q`. -/
theorem canonicalExponentSlotLabel_exists
    (n q : ℕ)
    (hq : q ∈ canonicalExponentSlotKernel.toDivisorTransitionKernel.index n) :
    ∃ L : PrimePowerLabel, L.q = q := by
  rcases canonicalExponentSlotLabels_mem_iff.mp hq with
    ⟨p, k, hp, hk_pos, _hk_le, hqpow⟩
  let L : PrimePowerLabel :=
    { q := q
      p := p
      k := k
      prime := hp
      k_pos := Nat.lt_of_lt_of_le Nat.zero_lt_one hk_pos
      eq_pow := hqpow }
  exact ⟨L, rfl⟩

/-- A chosen witness label for the canonical exponent-slot index. -/
noncomputable def canonicalExponentSlotLabel
    (n q : ℕ)
    (hq : q ∈ canonicalExponentSlotKernel.toDivisorTransitionKernel.index n) :
    PrimePowerLabel :=
  Classical.choose (canonicalExponentSlotLabel_exists n q hq)

@[simp] theorem canonicalExponentSlotLabel_q
    (n q : ℕ)
    (hq : q ∈ canonicalExponentSlotKernel.toDivisorTransitionKernel.index n) :
    (canonicalExponentSlotLabel n q hq).q = q :=
  Classical.choose_spec (canonicalExponentSlotLabel_exists n q hq)

/-- The canonical witness provider for the canonical exponent-slot kernel. -/
noncomputable def canonicalExponentSlotWitnessProvider :
    PrimePowerWitnessProvider canonicalExponentSlotKernel where
  label := canonicalExponentSlotLabel
  label_q := canonicalExponentSlotLabel_q

/-- The canonical full-channel choice for the canonical exponent-slot kernel. -/
def canonicalExponentSlotFullChannelSet :
    FullPrimePowerChannelSet canonicalExponentSlotKernel :=
  FullPrimePowerChannelSet.canonical canonicalExponentSlotKernel

/-- The canonical full-channel set is exactly the exponent-slot channel set. -/
theorem canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet :
    FullExponentSlotChannelSet canonicalExponentSlotFullChannelSet := by
  constructor
  intro _n _q
  exact canonicalExponentSlotLabels_mem_iff

/-- The canonical exponent-slot kernel has a full Markov shadow. -/
noncomputable def canonicalExponentSlotMarkovShadow :
    MarkovShadow LogCapacityState ℕ :=
  canonicalExponentSlotWitnessProvider
    |>.fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet
      canonicalExponentSlotFullChannelSet
      canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet

end DkMath.NumberTheory.PrimitiveSet
