/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily"

namespace DkMath.Collatz

/-!
# Canonical families of universal payment blocks

This module moves from one exact universal block to its canonical finite
family.  All results remain finite or cofinal statements about orbit-time
indices.  They do not assert a global sign for the sum of block drifts.
-/

/-- The endpoint sequence is strictly monotone. -/
theorem strictMono_paymentEndpointSeq (n : OddNat) :
    StrictMono (paymentEndpointSeq n) :=
  strictMono_nat_of_lt_succ (paymentEndpointSeq_lt_succ n)

/-- Linear lower bound measured from the first canonical endpoint. -/
theorem paymentEndpointSeq_zero_add_le (n : OddNat) (k : ℕ) :
    paymentEndpointSeq n 0 + k ≤ paymentEndpointSeq n k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := paymentEndpointSeq_lt_succ n k
      omega

/-- Simpler index lower bound for canonical endpoints. -/
theorem le_paymentEndpointSeq (n : OddNat) (k : ℕ) :
    k ≤ paymentEndpointSeq n k := by
  have h := paymentEndpointSeq_zero_add_le n k
  omega

/-- Canonical endpoints are cofinal in orbit time. -/
theorem exists_le_paymentEndpointSeq (n : OddNat) (t : ℕ) :
    ∃ k, t ≤ paymentEndpointSeq n k :=
  ⟨t, le_paymentEndpointSeq n t⟩

/-- The `k`-th endpoint-aligned universal payment block. -/
noncomputable def canonicalPaymentBlock (n : OddNat) : ℕ → Finset ℕ
  | 0 => Finset.Icc 0 (paymentEndpointSeq n 0)
  | k + 1 => Finset.Icc (paymentEndpointSeq n k + 1) (paymentEndpointSeq n (k + 1))

/-- The first canonical block is exactly the first universal target fiber. -/
theorem canonicalPaymentBlock_zero_eq_sourceFiber (n : OddNat) :
    canonicalPaymentBlock n 0 =
      orbitPaymentSourceFiberAt n (paymentEndpointSeq n 0) := by
  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
    (paymentEndpointSeq n 0) (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0)]
  simp [canonicalPaymentBlock, universalPaymentBlockStart_paymentEndpointSeq_zero]

/-- Every successor canonical block is exactly its endpoint's universal target fiber. -/
theorem canonicalPaymentBlock_succ_eq_sourceFiber (n : OddNat) (k : ℕ) :
    canonicalPaymentBlock n (k + 1) =
      orbitPaymentSourceFiberAt n (paymentEndpointSeq n (k + 1)) := by
  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
    (paymentEndpointSeq n (k + 1))
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1))]
  simp [canonicalPaymentBlock, universalPaymentBlockStart_paymentEndpointSeq_succ]

/-- Every canonical block is its endpoint's universal target fiber. -/
theorem canonicalPaymentBlock_eq_sourceFiber (n : OddNat) (k : ℕ) :
    canonicalPaymentBlock n k = orbitPaymentSourceFiberAt n (paymentEndpointSeq n k) := by
  cases k with
  | zero => exact canonicalPaymentBlock_zero_eq_sourceFiber n
  | succ k => exact canonicalPaymentBlock_succ_eq_sourceFiber n k

/-- Membership in a canonical block is exactly equality of the universal target. -/
theorem mem_canonicalPaymentBlock_iff_target_eq
    {n : OddNat} {k i : ℕ} :
    i ∈ canonicalPaymentBlock n k ↔ orbitPaymentTarget n i = paymentEndpointSeq n k := by
  rw [canonicalPaymentBlock_eq_sourceFiber, mem_orbitPaymentSourceFiberAt_iff_target_eq]

/-- Distinct canonical blocks are disjoint. -/
theorem disjoint_canonicalPaymentBlock_of_ne
    (n : OddNat) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n l) := by
  rw [Finset.disjoint_left]
  intro i hik hil
  have hk := (mem_canonicalPaymentBlock_iff_target_eq.mp hik)
  have hl := (mem_canonicalPaymentBlock_iff_target_eq.mp hil)
  have heq : paymentEndpointSeq n k = paymentEndpointSeq n l := hk.symm.trans hl
  exact hkl ((strictMono_paymentEndpointSeq n).injective heq)

/-- In particular, adjacent canonical blocks are disjoint. -/
theorem disjoint_canonicalPaymentBlock_succ (n : OddNat) (k : ℕ) :
    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n (k + 1)) :=
  disjoint_canonicalPaymentBlock_of_ne n (by omega)

/-- Recursive union of the canonical blocks through index `m`. -/
noncomputable def canonicalPaymentBlockPrefix (n : OddNat) : ℕ → Finset ℕ
  | 0 => canonicalPaymentBlock n 0
  | m + 1 => canonicalPaymentBlockPrefix n m ∪ canonicalPaymentBlock n (m + 1)

/-- Canonical blocks cover exactly the initial interval through their last endpoint. -/
theorem canonicalPaymentBlockPrefix_eq_Icc (n : OddNat) (m : ℕ) :
    canonicalPaymentBlockPrefix n m = Finset.Icc 0 (paymentEndpointSeq n m) := by
  induction m with
  | zero => simp [canonicalPaymentBlockPrefix, canonicalPaymentBlock]
  | succ m ih =>
      rw [canonicalPaymentBlockPrefix, ih]
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc]
      simp [canonicalPaymentBlock]
      have hstep := paymentEndpointSeq_lt_succ n m
      omega

/-- Membership in a finite block prefix is membership in one indexed block. -/
theorem mem_canonicalPaymentBlockPrefix_iff_exists
    {n : OddNat} {m i : ℕ} :
    i ∈ canonicalPaymentBlockPrefix n m ↔
      ∃ k, k ≤ m ∧ i ∈ canonicalPaymentBlock n k := by
  induction m with
  | zero =>
      simp [canonicalPaymentBlockPrefix]
  | succ m ih =>
      rw [canonicalPaymentBlockPrefix, Finset.mem_union, ih]
      constructor
      · rintro (⟨k, hkm, hik⟩ | hik)
        · exact ⟨k, hkm.trans (Nat.le_succ m), hik⟩
        · exact ⟨m + 1, le_rfl, hik⟩
      · rintro ⟨k, hkm, hik⟩
        rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
        · exact Or.inr hik
        · exact Or.inl ⟨k, by omega, hik⟩

/-- Every orbit time belongs to at least one canonical payment block. -/
theorem exists_mem_canonicalPaymentBlock (n : OddNat) (i : ℕ) :
    ∃ k, i ∈ canonicalPaymentBlock n k := by
  rcases exists_le_paymentEndpointSeq n i with ⟨m, him⟩
  have hiprefix : i ∈ canonicalPaymentBlockPrefix n m := by
    rw [canonicalPaymentBlockPrefix_eq_Icc]
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le i, him⟩
  rcases mem_canonicalPaymentBlockPrefix_iff_exists.mp hiprefix with ⟨k, _, hik⟩
  exact ⟨k, hik⟩

/-- Every orbit time belongs to exactly one canonical payment block. -/
theorem existsUnique_mem_canonicalPaymentBlock (n : OddNat) (i : ℕ) :
    ∃! k, i ∈ canonicalPaymentBlock n k := by
  rcases exists_mem_canonicalPaymentBlock n i with ⟨k, hik⟩
  refine ⟨k, hik, ?_⟩
  intro l hil
  have hk := mem_canonicalPaymentBlock_iff_target_eq.mp hik
  have hl := mem_canonicalPaymentBlock_iff_target_eq.mp hil
  exact (strictMono_paymentEndpointSeq n).injective (hl.symm.trans hk)

/-- Extra-height endpoints are exactly, and uniquely, the canonical endpoint sequence. -/
theorem two_le_orbitWindowHeight_iff_existsUnique_paymentEndpointSeq
    (n : OddNat) (j : ℕ) :
    2 ≤ orbitWindowHeight n j ↔ ∃! k, paymentEndpointSeq n k = j := by
  constructor
  · intro hheight
    rcases existsUnique_mem_canonicalPaymentBlock n j with ⟨k, hjk, _⟩
    refine ⟨k, ?_, ?_⟩
    · have htarget := mem_canonicalPaymentBlock_iff_target_eq.mp hjk
      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight] at htarget
      exact htarget.symm
    · intro l hlj
      have htarget := mem_canonicalPaymentBlock_iff_target_eq.mp hjk
      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight] at htarget
      exact (strictMono_paymentEndpointSeq n).injective (hlj.trans htarget)
  · rintro ⟨k, hk, _⟩
    rw [← hk]
    exact two_le_orbitWindowHeight_paymentEndpointSeq n k

/-- Exact endpoint-aligned signed drift telescope over the first `m + 1` blocks. -/
theorem sum_universalPaymentBlockSignedDriftAt_paymentEndpointSeq
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
      universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k)) =
        (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
          bitWidth n.1 := by
  induction m with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
        (paymentEndpointSeq n 0)
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0)]
      rw [universalPaymentBlockStart_paymentEndpointSeq_zero]
      change (bitWidth (iterateT (paymentEndpointSeq n 0 + 1) n).1 : ℤ) -
          bitWidth n.1 =
        (bitWidth (iterateT (paymentEndpointSeq n 0 + 1) n).1 : ℤ) -
          bitWidth n.1
      rfl
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
        (paymentEndpointSeq n (m + 1))
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (m + 1))]
      rw [universalPaymentBlockStart_paymentEndpointSeq_succ]
      ring

/-- The delayed-debt, endpoint-claim, and capacity term for block `k`. -/
noncomputable def endpointAccountingTerm (n : OddNat) (k : ℕ) : ℤ :=
  (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
    (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card -
      extraPaymentCapacityAt n (paymentEndpointSeq n k)

/-- Each endpoint accounting term is exactly that block's signed drift. -/
theorem endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      universalPaymentBlockSignedDriftAt n (paymentEndpointSeq n k) := by
  exact (universalPaymentBlockSignedDriftAt_eq_growthDebt_add_endpoint_sub_capacity
    n (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).symm

/-- Cumulative delayed-debt/capacity form of the endpoint-aligned telescope. -/
theorem sum_endpointAccountingTerm_paymentEndpointSeq
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
        bitWidth n.1 := by
  simp_rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  exact sum_universalPaymentBlockSignedDriftAt_paymentEndpointSeq n m

end DkMath.Collatz
