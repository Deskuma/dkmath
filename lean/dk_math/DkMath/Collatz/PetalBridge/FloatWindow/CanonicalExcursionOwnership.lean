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

/-- Internal spare tokens whose successor has zero signed drift. -/
noncomputable def canonicalInternalSaturatedZeroSpareIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalInternalSaturatedSpareIndices n q m).filter fun k =>
    endpointAccountingTerm n (k + 1) = 0

/-- Internal spare tokens whose successor has strictly positive signed drift. -/
noncomputable def canonicalInternalSaturatedPositiveSpareIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalInternalSaturatedSpareIndices n q m).filter fun k =>
    0 < endpointAccountingTerm n (k + 1)

@[simp] theorem mem_canonicalInternalSaturatedZeroSpareIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalInternalSaturatedZeroSpareIndices n q m ↔
      k ∈ canonicalInternalSaturatedSpareIndices n q m ∧
        endpointAccountingTerm n (k + 1) = 0 := by
  simp [canonicalInternalSaturatedZeroSpareIndices]

@[simp] theorem mem_canonicalInternalSaturatedPositiveSpareIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m ↔
      k ∈ canonicalInternalSaturatedSpareIndices n q m ∧
        0 < endpointAccountingTerm n (k + 1) := by
  simp [canonicalInternalSaturatedPositiveSpareIndices]

/-- Spare successors are exhausted by the zero and positive drift branches. -/
theorem canonicalInternalSaturatedSpareIndices_eq_zero_union_positive
    (n : OddNat) (q m : ℕ) :
    canonicalInternalSaturatedSpareIndices n q m =
      canonicalInternalSaturatedZeroSpareIndices n q m ∪
        canonicalInternalSaturatedPositiveSpareIndices n q m := by
  classical
  ext k
  constructor
  · intro hk
    have hkFull := Finset.mem_of_mem_erase hk
    have hnonneg :=
      (mem_canonicalSaturatedSpareSuccessorIndices.mp hkFull).2.1
    by_cases hz : endpointAccountingTerm n (k + 1) = 0
    · exact Finset.mem_union_left _
        (mem_canonicalInternalSaturatedZeroSpareIndices.mpr ⟨hk, hz⟩)
    · exact Finset.mem_union_right _
        (mem_canonicalInternalSaturatedPositiveSpareIndices.mpr
          ⟨hk, by omega⟩)
  · intro hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (mem_canonicalInternalSaturatedZeroSpareIndices.mp hk).1
    · exact (mem_canonicalInternalSaturatedPositiveSpareIndices.mp hk).1

/-- Zero- and positive-successor spare tokens are disjoint. -/
theorem canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare
    (n : OddNat) (q m : ℕ) :
    Disjoint (canonicalInternalSaturatedZeroSpareIndices n q m)
      (canonicalInternalSaturatedPositiveSpareIndices n q m) := by
  classical
  rw [Finset.disjoint_left]
  intro k hk0 hkp
  have hz := (mem_canonicalInternalSaturatedZeroSpareIndices.mp hk0).2
  have hp := (mem_canonicalInternalSaturatedPositiveSpareIndices.mp hkp).2
  omega

/-- Exact cardinality split of the internal spare class by successor drift. -/
theorem card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive
    (n : OddNat) (q m : ℕ) :
    (canonicalInternalSaturatedSpareIndices n q m).card =
      (canonicalInternalSaturatedZeroSpareIndices n q m).card +
        (canonicalInternalSaturatedPositiveSpareIndices n q m).card := by
  rw [canonicalInternalSaturatedSpareIndices_eq_zero_union_positive,
    Finset.card_union_of_disjoint
      (canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare n q m)]

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

/-! ## Positive-spare absorption in the existing selected carrier -/

/-- Actual same-block drift-image incidences over the positive blocks in the
window.  Saturated blocks contribute an empty image. -/
def CanonicalGlobalSelectedDriftImageCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
      i ∈ canonicalSelectedDriftImageCarrier n k.val}

/-- The resources charged in cp-347: existing drift images together with one
predecessor token for each internal positive-spare successor. -/
def CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier
    (n : OddNat) (q m : ℕ) :=
  CanonicalGlobalSelectedDriftImageCarrier n q m ⊕
    {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}

/-- Forget only the image-membership proof, retaining block and incidence. -/
def canonicalGlobalSelectedDriftImageInclusion
    (n : OddNat) (q m : ℕ) :
    CanonicalGlobalSelectedDriftImageCarrier n q m ↪
      CanonicalGlobalSelectedPressureCarrier n q m :=
  (Function.Embedding.refl _).sigmaMap fun k =>
    Function.Embedding.subtype fun i =>
      i ∈ canonicalSelectedDriftImageCarrier n k.val

/-- Charge one positive-spare predecessor to an actual spare incidence in its
successor block. -/
noncomputable def canonicalInternalPositiveSpareCharge
    (n : OddNat) (q m : ℕ) :
    {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m} →
      CanonicalGlobalSelectedPressureCarrier n q m := fun k => by
  classical
  have hk :=
    (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).1
  have hkFull := Finset.mem_of_mem_erase hk
  have hkClass := mem_canonicalSaturatedSpareSuccessorIndices.mp hkFull
  have hkInternal : k.val < m := by
    have hne := (Finset.mem_erase.mp hk).1
    have hle := (Finset.mem_Icc.mp
      (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1).2
    omega
  have hqk := (Finset.mem_Icc.mp
    (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1).1
  have hpos :=
    (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).2
  let e := oneEmbedding_successorSpareCarrier hkClass.2.2
  exact ⟨⟨k.val + 1, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpos⟩⟩, (e 0).1⟩

/-- The positive-spare charge keeps the successor block coordinate. -/
@[simp] theorem canonicalInternalPositiveSpareCharge_fst
    {n : OddNat} {q m : ℕ}
    (k : {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}) :
    (canonicalInternalPositiveSpareCharge n q m k).1.val = k.val + 1 := by
  simp [canonicalInternalPositiveSpareCharge]

/-- The charged incidence lies in the complement of the same-block drift
image. -/
theorem canonicalInternalPositiveSpareCharge_mem_spare
    {n : OddNat} {q m : ℕ}
    (k : {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}) :
    (canonicalInternalPositiveSpareCharge n q m k).2 ∈
      canonicalSelectedDriftSpareCarrier n (k.val + 1) := by
  classical
  simp only [canonicalInternalPositiveSpareCharge]
  exact (oneEmbedding_successorSpareCarrier
    (mem_canonicalSaturatedSpareSuccessorIndices.mp
      (Finset.mem_of_mem_erase
        (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).1)).2.2
      0).property

/-- Drift images and predecessor positive-spare charges embed without reuse
into the existing positive-only global selected carrier.  The sigma coordinate
retains the successor block; the cross-summand case is impossible because the
second summand lands in the complement of the first summand's image. -/
noncomputable def canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding
    (n : OddNat) (q m : ℕ) :
    CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier n q m ↪
      CanonicalGlobalSelectedPressureCarrier n q m where
  toFun := Sum.elim (canonicalGlobalSelectedDriftImageInclusion n q m)
    (canonicalInternalPositiveSpareCharge n q m)
  inj' := by
    classical
    apply Function.Injective.sumElim
    · exact (canonicalGlobalSelectedDriftImageInclusion n q m).injective
    · intro a b hab
      apply Subtype.ext
      have hindex := congrArg (fun z => z.1.val) hab
      change a.val + 1 = b.val + 1 at hindex
      omega
    · intro a b hab
      have himage :
          (canonicalGlobalSelectedDriftImageInclusion n q m a).2 ∈
            canonicalSelectedDriftImageCarrier n
              (canonicalGlobalSelectedDriftImageInclusion n q m a).1.val :=
        a.2.property
      rw [hab] at himage
      have hspare : (canonicalInternalPositiveSpareCharge n q m b).2 ∈
          canonicalSelectedDriftSpareCarrier n
            (canonicalInternalPositiveSpareCharge n q m b).1.val := by
        simpa only [canonicalInternalPositiveSpareCharge_fst] using
          canonicalInternalPositiveSpareCharge_mem_spare b
      exact (Finset.mem_sdiff.mp hspare).2 himage

/-- Cardinality form of the no-reuse positive-spare absorption certificate. -/
theorem natCard_globalSelectedDriftImage_add_internalPositiveSpare_le_globalSelected
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) +
        (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) := by
  classical
  letI : Fintype {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m} :=
    Fintype.ofFinset (canonicalPositiveDriftBlockIndices n q m) (by simp)
  letI (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  letI (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  letI : Fintype (CanonicalGlobalSelectedDriftImageCarrier n q m) := by
    unfold CanonicalGlobalSelectedDriftImageCarrier
    infer_instance
  letI : Fintype
      {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m} :=
    Fintype.ofFinset (canonicalInternalSaturatedPositiveSpareIndices n q m)
      (by simp)
  letI : Fintype (CanonicalGlobalSelectedPressureCarrier n q m) := by
    unfold CanonicalGlobalSelectedPressureCarrier
    infer_instance
  have hcard := Nat.card_le_card_of_injective
    (canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding n q m)
    (canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding n q m).injective
  rw [CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier,
    Nat.card_sum] at hcard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

/-- A positive block's reflected drift is exactly its chosen drift image plus
its possible saturated unit. -/
theorem intToNat_endpointAccountingTerm_eq_driftImage_add_saturatedToken
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    Int.toNat (endpointAccountingTerm n k) =
      (canonicalSelectedDriftImageCarrier n k).card +
        canonicalSaturatedTokenNat n k := by
  classical
  by_cases hs : CanonicalSaturatedBorderBlock n k
  · rw [hs.netDrift_eq_one]
    simp [canonicalSelectedDriftImageCarrier,
      canonicalSaturatedTokenNat, canonicalSaturatedUnit, hs]
  · rw [card_canonicalSelectedDriftImageCarrier hpos hs]
    simp [canonicalSaturatedTokenNat, canonicalSaturatedUnit, hs]

/-- Exact cardinality of the global chosen drift-image carrier. -/
theorem natCard_CanonicalGlobalSelectedDriftImageCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) =
      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        (canonicalSelectedDriftImageCarrier n k).card := by
  classical
  unfold CanonicalGlobalSelectedDriftImageCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
    fun k => (canonicalSelectedDriftImageCarrier n k).card

/-- Saturated-token naturals sum to the saturated block count. -/
theorem sum_canonicalSaturatedTokenNat_eq_saturatedCard
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        canonicalSaturatedTokenNat n k) =
      (canonicalSaturatedBlockIndices n q m).card := by
  classical
  simp only [canonicalSaturatedTokenNat, canonicalSaturatedUnit]
  have htoken (k : ℕ) :
      (if CanonicalSaturatedBorderBlock n k then (1 : ℤ) else 0).toNat =
        if CanonicalSaturatedBorderBlock n k then 1 else 0 := by
    by_cases hs : CanonicalSaturatedBorderBlock n k <;> simp [hs]
  simp_rw [htoken]
  rw [Finset.sum_boole]
  have hsets :
      (canonicalPositiveDriftBlockIndices n q m).filter
          (CanonicalSaturatedBorderBlock n) =
        canonicalSaturatedBlockIndices n q m := by
    ext k
    simp only [canonicalPositiveDriftBlockIndices,
      canonicalSaturatedBlockIndices, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, _⟩, hs⟩
      exact ⟨hk, hs⟩
    · rintro ⟨hk, hs⟩
      exact ⟨⟨hk, hs.drift_pos⟩, hs⟩
  rw [hsets]
  exact_mod_cast rfl

/-- Positive reflected mass splits exactly into chosen nonsaturated images and
the isolated saturated units. -/
theorem sum_intToNat_positiveDrift_eq_globalDriftImage_add_saturatedCard
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k)) =
      Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) +
        (canonicalSaturatedBlockIndices n q m).card := by
  rw [natCard_CanonicalGlobalSelectedDriftImageCarrier,
    ← sum_canonicalSaturatedTokenNat_eq_saturatedCard,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact intToNat_endpointAccountingTerm_eq_driftImage_add_saturatedToken
    ((Finset.mem_filter.mp hk).2)

/-- Positive drift together with internal positive-spare predecessors fits in
the existing global selected carrier plus the isolated saturated units. -/
theorem sum_intToNat_positiveDrift_add_internalPositiveSpare_le_global_add_saturated
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k)) +
        (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (canonicalSaturatedBlockIndices n q m).card := by
  have himage :=
    natCard_globalSelectedDriftImage_add_internalPositiveSpare_le_globalSelected
      n q m
  rw [sum_intToNat_positiveDrift_eq_globalDriftImage_add_saturatedCard]
  omega

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

/-- Improved current-window ownership: positive-successor spare tokens are
absorbed by unused incidences of their positive successor blocks.  Only the
genuinely zero-drift spare class remains explicit. -/
theorem CanonicalOpenPositiveQueueExcursion.queue_le_globalSelected_add_zeroSpare_rigid_terminal
    {n : OddNat} {q m : ℕ}
    (h : CanonicalOpenPositiveQueueExcursion n q m) :
    (canonicalOutstandingClaimQueue n m : ℤ) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (canonicalInternalSaturatedZeroSpareIndices n q m).card +
          canonicalInternalRigidSaturatedResidualCount n q m +
            canonicalTerminalSaturatedIndicator n m := by
  have hmass := h.queue_eq_positiveMass_sub_negativeMass
  have habsorbNat :=
    sum_intToNat_positiveDrift_add_internalPositiveSpare_le_global_add_saturated
      n q m
  have hpositiveCast : canonicalPositiveDriftMass n q m =
      ((∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) := by
    rw [canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hpos := (Finset.mem_filter.mp hk).2
    rw [Int.toNat_of_nonneg hpos.le]
  have habsorb : canonicalPositiveDriftMass n q m +
      (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
        (Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) : ℤ) +
          (canonicalSaturatedBlockIndices n q m).card := by
    rw [hpositiveCast]
    exact_mod_cast habsorbNat
  have hsplit :=
    canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
      n q m h.1
  have hspareSplit :=
    card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive n q m
  have hnegative :=
    card_canonicalInternalSaturatedNegativeIndices_le_negativeMass n q m
  unfold canonicalSaturatedTokenCount at hsplit
  omega

/-!
The stronger target without every spare residual cannot be obtained by
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

Neither contract is currently available.  cp-347 does absorb the strictly
positive successor branch by its actual spare complement, but treating the
remaining zero-spare branch as if it were in the positive-only carrier would
still be a type-invalid ownership claim.

The companion finite audit over odd roots through `16383` found zero-drift
spare successors (the first record-window witness has root `3931`, predecessor
block `0`, successor block `1`, and spare cardinality `1`).  This observation
is not a theorem, but it rules out using finite evidence to motivate an
impossibility lemma.  A later checkpoint that removes this residual must add a
selected-arrival carrier admitting zero-drift blocks; it must not weaken the
positive-only index contract proved here.
-/

end DkMath.Collatz
