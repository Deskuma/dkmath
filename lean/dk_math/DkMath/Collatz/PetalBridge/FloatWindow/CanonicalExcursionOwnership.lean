/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership"

namespace DkMath.Collatz

/-!
# Current-window ownership of saturated excursion tokens

This module separates saturated tokens whose successors remain in `q..m` from
the possible token at `m`.  It does not spend the successor block `m+1`.
-/

/-- Saturated tokens whose immediate successor remains in the observed window. -/
noncomputable def canonicalInternalSaturatedIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedBlockIndices n q m).erase m

/-- Internal negative-successor tokens. -/
noncomputable def canonicalInternalSaturatedNegativeIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedNegativeSuccessorIndices n q m).erase m

/-- Internal spare-successor tokens. -/
noncomputable def canonicalInternalSaturatedSpareIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedSpareSuccessorIndices n q m).erase m

/-- Internal zero-rigid successor tokens. -/
noncomputable def canonicalInternalSaturatedZeroRigidIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedZeroRigidSuccessorIndices n q m).erase m

/-- Internal tight-positive-rigid successor tokens. -/
noncomputable def canonicalInternalSaturatedTightRigidIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedTightRigidSuccessorIndices n q m).erase m

/-- Visible internal rigid successor residual. -/
noncomputable def canonicalInternalRigidSaturatedResidualCount
    (n : OddNat) (q m : ℕ) : ℕ :=
  (canonicalInternalSaturatedZeroRigidIndices n q m).card +
    (canonicalInternalSaturatedTightRigidIndices n q m).card

/-- The one-bit temporal residual at the right endpoint. -/
noncomputable def canonicalTerminalSaturatedIndicator
    (n : OddNat) (m : ℕ) : ℕ :=
  by
    classical
    exact if CanonicalSaturatedBorderBlock n m then 1 else 0

@[simp] theorem mem_canonicalInternalSaturatedIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalInternalSaturatedIndices n q m ↔
      k ∈ canonicalSaturatedBlockIndices n q m ∧ k < m := by
  rw [canonicalInternalSaturatedIndices, Finset.mem_erase]
  constructor
  · rintro ⟨hne, hk⟩
    have hkm := (Finset.mem_Icc.mp
      (mem_canonicalSaturatedBlockIndices.mp hk).1).2
    exact ⟨hk, by omega⟩
  · rintro ⟨hk, hlt⟩
    exact ⟨by omega, hk⟩

/-- The terminal residual is at most one. -/
theorem canonicalTerminalSaturatedIndicator_le_one
    (n : OddNat) (m : ℕ) :
    canonicalTerminalSaturatedIndicator n m ≤ 1 := by
  classical
  unfold canonicalTerminalSaturatedIndicator
  split <;> omega

/-- Erasing the right endpoint leaves exactly the internal priority
classification. -/
theorem canonicalInternalSaturatedSuccessorIndices_union_eq
    (n : OddNat) (q m : ℕ) :
    canonicalInternalSaturatedNegativeIndices n q m ∪
        canonicalInternalSaturatedSpareIndices n q m ∪
          canonicalInternalSaturatedZeroRigidIndices n q m ∪
            canonicalInternalSaturatedTightRigidIndices n q m =
      canonicalInternalSaturatedIndices n q m := by
  classical
  simp only [canonicalInternalSaturatedNegativeIndices,
    canonicalInternalSaturatedSpareIndices,
    canonicalInternalSaturatedZeroRigidIndices,
    canonicalInternalSaturatedTightRigidIndices,
    canonicalInternalSaturatedIndices]
  rw [← Finset.erase_union_distrib, ← Finset.erase_union_distrib,
    ← Finset.erase_union_distrib,
    canonicalSaturatedSuccessorIndices_union_eq]

/-- Exact internal class count; the two rigid modes remain visible. -/
theorem card_canonicalInternalSaturatedIndices_eq_classCounts
    (n : OddNat) (q m : ℕ) :
    (canonicalInternalSaturatedIndices n q m).card =
      (canonicalInternalSaturatedNegativeIndices n q m).card +
        (canonicalInternalSaturatedSpareIndices n q m).card +
          canonicalInternalRigidSaturatedResidualCount n q m := by
  classical
  let N := canonicalInternalSaturatedNegativeIndices n q m
  let S := canonicalInternalSaturatedSpareIndices n q m
  let Z := canonicalInternalSaturatedZeroRigidIndices n q m
  let T := canonicalInternalSaturatedTightRigidIndices n q m
  have hdisjoint (A B : Finset ℕ) (h : Disjoint A B) :
      Disjoint (A.erase m) (B.erase m) :=
    h.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hNS : Disjoint N S := hdisjoint _ _
    (canonicalSaturatedNegative_disjoint_spare n q m)
  have hNZ : Disjoint N Z := hdisjoint _ _
    (canonicalSaturatedNegative_disjoint_rigid n q m).1
  have hNT : Disjoint N T := hdisjoint _ _
    (canonicalSaturatedNegative_disjoint_rigid n q m).2
  have hSZ : Disjoint S Z := hdisjoint _ _
    (canonicalSaturatedSpare_disjoint_rigid n q m).1
  have hST : Disjoint S T := hdisjoint _ _
    (canonicalSaturatedSpare_disjoint_rigid n q m).2
  have hZT : Disjoint Z T := hdisjoint _ _
    (canonicalSaturatedZeroRigid_disjoint_tightRigid n q m)
  have hN_SZT : Disjoint N (S ∪ (Z ∪ T)) := by
    rw [Finset.disjoint_left]
    intro x hxN hx
    rcases Finset.mem_union.mp hx with hxS | hx
    · exact Finset.disjoint_left.mp hNS hxN hxS
    · rcases Finset.mem_union.mp hx with hxZ | hxT
      · exact Finset.disjoint_left.mp hNZ hxN hxZ
      · exact Finset.disjoint_left.mp hNT hxN hxT
  have hS_ZT : Disjoint S (Z ∪ T) := by
    rw [Finset.disjoint_left]
    intro x hxS hx
    rcases Finset.mem_union.mp hx with hxZ | hxT
    · exact Finset.disjoint_left.mp hSZ hxS hxZ
    · exact Finset.disjoint_left.mp hST hxS hxT
  have hunion : N ∪ (S ∪ (Z ∪ T)) = canonicalInternalSaturatedIndices n q m := by
    simpa [N, S, Z, T, Finset.union_assoc] using
      canonicalInternalSaturatedSuccessorIndices_union_eq n q m
  rw [← hunion]
  calc
    (N ∪ (S ∪ (Z ∪ T))).card = N.card + (S ∪ (Z ∪ T)).card :=
      Finset.card_union_of_disjoint hN_SZT
    _ = N.card + (S.card + (Z ∪ T).card) := by
      rw [Finset.card_union_of_disjoint hS_ZT]
    _ = N.card + (S.card + (Z.card + T.card)) := by
      rw [Finset.card_union_of_disjoint hZT]
    _ = (canonicalInternalSaturatedNegativeIndices n q m).card +
          (canonicalInternalSaturatedSpareIndices n q m).card +
            canonicalInternalRigidSaturatedResidualCount n q m := by
      simp only [canonicalInternalRigidSaturatedResidualCount, N, S, Z, T]
      omega

/-- Exact current-window temporal split. -/
theorem canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
    (n : OddNat) (q m : ℕ) (hqm : q ≤ m) :
    canonicalSaturatedTokenCount n q m =
      (canonicalInternalSaturatedNegativeIndices n q m).card +
        (canonicalInternalSaturatedSpareIndices n q m).card +
          canonicalInternalRigidSaturatedResidualCount n q m +
            canonicalTerminalSaturatedIndicator n m := by
  have hinternal := card_canonicalInternalSaturatedIndices_eq_classCounts n q m
  classical
  by_cases hs : CanonicalSaturatedBorderBlock n m
  · have hm : m ∈ canonicalSaturatedBlockIndices n q m :=
      mem_canonicalSaturatedBlockIndices.mpr
        ⟨Finset.mem_Icc.mpr ⟨hqm, le_rfl⟩, hs⟩
    have herase := Finset.card_erase_add_one hm
    have hinternal' :
        ((canonicalSaturatedBlockIndices n q m).erase m).card =
          (canonicalInternalSaturatedNegativeIndices n q m).card +
            (canonicalInternalSaturatedSpareIndices n q m).card +
              canonicalInternalRigidSaturatedResidualCount n q m := by
      simpa [canonicalInternalSaturatedIndices] using hinternal
    unfold canonicalSaturatedTokenCount canonicalTerminalSaturatedIndicator
    rw [if_pos hs]
    omega
  · have hm : m ∉ canonicalSaturatedBlockIndices n q m := by
      intro hm
      exact hs (mem_canonicalSaturatedBlockIndices.mp hm).2
    have hinternal' :
        ((canonicalSaturatedBlockIndices n q m).erase m).card =
          (canonicalInternalSaturatedNegativeIndices n q m).card +
            (canonicalInternalSaturatedSpareIndices n q m).card +
              canonicalInternalRigidSaturatedResidualCount n q m := by
      simpa [canonicalInternalSaturatedIndices] using hinternal
    unfold canonicalSaturatedTokenCount canonicalTerminalSaturatedIndicator
    rw [if_neg hs] at *
    rw [Finset.erase_eq_of_notMem hm] at hinternal'
    omega

/-! ## Internal negative payment -/

/-- Negative-drift units in the current interval, indexed by their block. -/
def CanonicalNegativeDriftUnitCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ j : {j : ℕ // j ∈ Finset.Icc q m},
    Fin (Int.toNat (max (-endpointAccountingTerm n j.val) 0))

/-- Each internal negative-successor token owns one distinct negative-mass
unit at its successor block. -/
noncomputable def canonicalInternalNegativeTokenEmbedding
    (n : OddNat) (q m : ℕ) :
    {k : ℕ // k ∈ canonicalInternalSaturatedNegativeIndices n q m} ↪
      CanonicalNegativeDriftUnitCarrier n q m where
  toFun k := by
    have hkFull := Finset.mem_of_mem_erase k.property
    have hk := mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull
    have hkInternal : k.val < m := by
      have hne := (Finset.mem_erase.mp k.property).1
      have hle := (Finset.mem_Icc.mp
        (mem_canonicalSaturatedBlockIndices.mp hk.1).1).2
      omega
    have hqk := (Finset.mem_Icc.mp
      (mem_canonicalSaturatedBlockIndices.mp hk.1).1).1
    refine ⟨⟨k.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ⟨0, ?_⟩⟩
    have hneg := hk.2
    have hmag : (1 : ℤ) ≤ max (-endpointAccountingTerm n (k.val + 1)) 0 := by
      omega
    have htoNat : 1 ≤ Int.toNat
        (max (-endpointAccountingTerm n (k.val + 1)) 0) := by
      have hcast := Int.toNat_of_nonneg
        (show 0 ≤ max (-endpointAccountingTerm n (k.val + 1)) 0 by omega)
      by_contra hnot
      have hzero : Int.toNat
          (max (-endpointAccountingTerm n (k.val + 1)) 0) = 0 := by omega
      rw [hzero] at hcast
      omega
    exact Nat.zero_lt_of_lt htoNat
  inj' := by
    intro a b hab
    have hindex := congrArg (fun z => z.1.1) hab
    change a.1 + 1 = b.1 + 1 at hindex
    apply Subtype.ext
    omega

/-- Internal negative successor tokens are paid by distinct negative-mass
units already present in `q..m`; no successor at `m+1` is used. -/
theorem card_canonicalInternalSaturatedNegativeIndices_le_negativeMass
    (n : OddNat) (q m : ℕ) :
    ((canonicalInternalSaturatedNegativeIndices n q m).card : ℤ) ≤
      canonicalNegativeDriftMass n q m := by
  classical
  let I := canonicalInternalSaturatedNegativeIndices n q m
  let J := I.image fun k => k + 1
  have hinj : ∀ a ∈ I, ∀ b ∈ I, a + 1 = b + 1 → a = b := by
    intro a _ b _ hab
    omega
  have hcard : J.card = I.card := Finset.card_image_iff.mpr hinj
  have hsubset : J ⊆ Finset.Icc q m := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkErase := Finset.mem_erase.mp hk
    have hkFull := Finset.mem_of_mem_erase hk
    have hkClass := mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull
    have hkIcc := Finset.mem_Icc.mp
      (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hunit :
      (∑ j ∈ J, (1 : ℤ)) ≤
        ∑ j ∈ J, max (-endpointAccountingTerm n j) 0 := by
    apply Finset.sum_le_sum
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkFull := Finset.mem_of_mem_erase hk
    have hneg :=
      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull).2
    omega
  have hwindow :
      (∑ j ∈ J, max (-endpointAccountingTerm n j) 0) ≤
        ∑ j ∈ Finset.Icc q m, max (-endpointAccountingTerm n j) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j _ _ => le_max_right _ _)
  unfold canonicalNegativeDriftMass
  have hones : (∑ _j ∈ J, (1 : ℤ)) = J.card := by simp
  rw [hones, hcard] at hunit
  exact hunit.trans hwindow

/-! ## Current ownership surface and remaining carrier mismatch -/

/-- Current-window ownership after internal negative cancellation.  The spare
count remains explicit because zero-drift spare successors are not indexed by
the existing positive-only global selected carrier. -/
theorem CanonicalOpenPositiveQueueExcursion.queue_le_globalSelected_add_internalSpare_rigid_terminal
    {n : OddNat} {q m : ℕ}
    (h : CanonicalOpenPositiveQueueExcursion n q m) :
    (canonicalOutstandingClaimQueue n m : ℤ) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (canonicalInternalSaturatedSpareIndices n q m).card +
          canonicalInternalRigidSaturatedResidualCount n q m +
            canonicalTerminalSaturatedIndicator n m := by
  have hmass := h.queue_eq_positiveMass_sub_negativeMass
  have hcarrierNat :=
    sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard n q m
  have hpositiveCast : canonicalPositiveDriftMass n q m =
      ((∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) := by
    rw [canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hpos := (Finset.mem_filter.mp hk).2
    rw [Int.toNat_of_nonneg hpos.le]
  have hcarrier : canonicalPositiveDriftMass n q m ≤
      (Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) : ℤ) +
        (canonicalSaturatedBlockIndices n q m).card := by
    rw [hpositiveCast]
    exact_mod_cast hcarrierNat
  have hsplit :=
    canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
      n q m h.1
  have hnegative :=
    card_canonicalInternalSaturatedNegativeIndices_le_negativeMass n q m
  unfold canonicalSaturatedTokenCount at hsplit
  omega

/-!
The stronger cp-346 target without `internalSpareCount` cannot be obtained by
the requested contribution-preserving embedding into
`CanonicalGlobalSelectedPressureCarrier n q m` from the current APIs.

That global carrier is sigma-indexed only by `canonicalPositiveDriftBlockIndices`.
But `CanonicalSaturatedBorderBlock.successor_source_classification` explicitly
permits a successor with zero drift and a nonempty selected carrier, and
`successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty` places
exactly that branch in `CanonicalSuccessorSpareAvailable`.  Such an incidence
has no positive-block index with which to inhabit the requested codomain.

Therefore removing `internalSpareCount` requires one of two new contracts:

* enlarge the global selected carrier to include zero-drift blocks; or
* prove that zero-drift spare successors cannot occur in the intended open
  excursions.

Neither contract is currently available.  Treating zero-spare as if it were
in the positive-only carrier would be a type-invalid ownership claim, so this
module stops at the theorem above.
-/

end DkMath.Collatz
