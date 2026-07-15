/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude"

namespace DkMath.Collatz

/-!
# Fixed-depth pressure amplitude reduction

This module transports the dynamic selected-incidence carrier into the
existing fixed-depth prefix fibers.  All transports below preserve source
incidences; none is interpreted as a future repayment allocation.
-/

/-! ## Block-preserving positive-drift incidence embedding -/

/-- The local certificate attached to one positive block: selected source
incidences, or the isolated saturated units of that same block. -/
def CanonicalLocalSelectedOrSaturatedCarrier
    (n : OddNat) (k : ℕ) :=
  {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} ⊕
    Fin (canonicalSaturatedTokenNat n k)

/-- A local finite embedding chosen from the pointwise cardinality theorem.
Unlike the earlier global cardinality embedding, this choice is made before
forming the block-indexed sigma, so it cannot move a unit to another block. -/
noncomputable def canonicalLocalPositiveDriftEmbedding
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    Fin (Int.toNat (endpointAccountingTerm n k)) ↪
      CanonicalLocalSelectedOrSaturatedCarrier n k := by
  classical
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  letI : Fintype (CanonicalLocalSelectedOrSaturatedCarrier n k) := by
    unfold CanonicalLocalSelectedOrSaturatedCarrier
    infer_instance
  have htargetCard :
      Fintype.card (CanonicalLocalSelectedOrSaturatedCarrier n k) =
        (canonicalSelectedPressureCarrier n k).card +
          canonicalSaturatedTokenNat n k := by
    unfold CanonicalLocalSelectedOrSaturatedCarrier
    calc
      Fintype.card
          ({i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} ⊕
            Fin (canonicalSaturatedTokenNat n k)) =
          Fintype.card {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} +
            Fintype.card (Fin (canonicalSaturatedTokenNat n k)) :=
        Fintype.card_sum
      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
  exact Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr (by
    rw [Fintype.card_fin, htargetCard]
    exact intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated hpos))

/-- Block-indexed target of the local incidence embeddings. -/
def CanonicalBlockPreservingIncidenceCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
    CanonicalLocalSelectedOrSaturatedCarrier n k.val

/-- Assemble the local maps without forgetting their canonical block. -/
noncomputable def canonicalBlockPreservingPositiveDriftEmbedding
    (n : OddNat) (q m : ℕ) :
    CanonicalPositiveDriftUnitCarrier n q m ↪
      CanonicalBlockPreservingIncidenceCarrier n q m :=
  (Function.Embedding.refl _).sigmaMap fun k =>
    canonicalLocalPositiveDriftEmbedding ((Finset.mem_filter.mp k.property).2)

/-- The assembled embedding preserves the source block definitionally. -/
@[simp] theorem canonicalBlockPreservingPositiveDriftEmbedding_fst
    {n : OddNat} {q m : ℕ}
    (x : CanonicalPositiveDriftUnitCarrier n q m) :
    (canonicalBlockPreservingPositiveDriftEmbedding n q m x).1 = x.1 :=
  rfl

/-- Compatibility note: the old theorem remains the coarser cardinality-only
surface; use `canonicalBlockPreservingPositiveDriftEmbedding` when block
identity matters. -/
theorem exists_positiveDriftUnitEmbedding_global_add_saturated_compat
    (n : OddNat) (q m : ℕ) :
    Nonempty (CanonicalPositiveDriftUnitCarrier n q m ↪
      (CanonicalGlobalSelectedPressureCarrier n q m ⊕
        {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m})) :=
  exists_positiveDriftUnitEmbedding_global_add_saturated n q m

/-! ## Active selected-depth support -/

/-- Positive nonsaturated blocks at selected depth `d`. -/
noncomputable def canonicalActiveSelectedPressureBlocksAtDepth
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalNonsaturatedPositiveBlockIndices n q m).filter fun k =>
    canonicalSelectedPositivePressureDepth n k = d

/-- Depths carrying at least one positive nonsaturated selected block. -/
noncomputable def canonicalActiveSelectedPressureDepthSupport
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalNonsaturatedPositiveBlockIndices n q m).image fun k =>
    canonicalSelectedPositivePressureDepth n k

@[simp] theorem mem_canonicalActiveSelectedPressureBlocksAtDepth
    {n : OddNat} {q m d k : ℕ} :
    k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d ↔
      k ∈ canonicalNonsaturatedPositiveBlockIndices n q m ∧
        canonicalSelectedPositivePressureDepth n k = d := by
  simp [canonicalActiveSelectedPressureBlocksAtDepth]

/-- Active support is exactly nonemptiness of the active block bucket. -/
theorem mem_activeSelectedPressureDepthSupport_iff_nonempty
    {n : OddNat} {q m d : ℕ} :
    d ∈ canonicalActiveSelectedPressureDepthSupport n q m ↔
      (canonicalActiveSelectedPressureBlocksAtDepth n q m d).Nonempty := by
  classical
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨k, hk, hkd⟩
    exact ⟨k, mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
      ⟨hk, hkd⟩⟩
  · rintro ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨k,
      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).1,
      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).2⟩

/-- Every active selected depth has a nonempty incidence bucket. -/
theorem activeSelectedPressureDepthSupport_bucketCarrier_nonempty
    {n : OddNat} {q m d : ℕ}
    (hd : d ∈ canonicalActiveSelectedPressureDepthSupport n q m) :
    Nonempty (CanonicalSelectedPressureBucketCarrier n q m d) := by
  classical
  rcases mem_activeSelectedPressureDepthSupport_iff_nonempty.mp hd with ⟨k, hk⟩
  have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
  have hpos := (mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1).2.1
  have hnot := (mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1).2.2
  have hcard := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
  have hcarrier : (canonicalSelectedPressureCarrier n k).Nonempty := by
    apply Finset.card_pos.mp
    have : 0 < (canonicalSelectedPressureCarrier n k).card := by
      exact_mod_cast hpos.trans_le hcard
    exact this
  rcases hcarrier with ⟨i, hi⟩
  refine ⟨⟨⟨k, ?_⟩, ⟨i, hi⟩⟩⟩
  exact mem_canonicalSelectedPressureBlocksAtDepth.mpr
    ⟨(Finset.mem_filter.mp hdata.1).1, hdata.2⟩

/-! ## Fixed-depth prefix embedding -/

/-- Forgetting the canonical block sends a selected bucket incidence into the
endpoint-aligned fixed-depth continuation fiber. -/
noncomputable def selectedPressureBucketToPrefixFiber
    {n : OddNat} {q m d : ℕ} (_hqm : q ≤ m) :
    CanonicalSelectedPressureBucketCarrier n q m d →
      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
        (paymentEndpointSeq n m + 1) (d + 1)} := by
  classical
  intro x
  refine ⟨x.2.val, ?_⟩
  have hfixed := x.mem_fixedDepthContinuationFiber
  have hblock := (mem_canonicalPaymentBlockContinuationFiber_iff.mp hfixed).1
  have hcont := (mem_canonicalPaymentBlockContinuationFiber_iff.mp hfixed).2
  have hkpos := (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1
  have hkIcc := (Finset.mem_filter.mp hkpos).1
  have hkm := (Finset.mem_Icc.mp hkIcc).2
  have hprefix : x.2.val ∈ canonicalPaymentBlockPrefix n m :=
    mem_canonicalPaymentBlockPrefix_iff_exists.mpr ⟨x.1.val, hkm, hblock⟩
  unfold orbitDepthContinuationRangeFiber
  apply Finset.mem_filter.mpr
  constructor
  · rw [← canonicalPaymentBlockPrefix_eq_range]
    exact hprefix
  · exact hcont

/-- The forget-block map is injective because source time determines its unique
canonical block. -/
theorem selectedPressureBucketToPrefixFiber_injective
    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
    Function.Injective (selectedPressureBucketToPrefixFiber
      (n := n) (q := q) (m := m) (d := d) hqm) := by
  intro x y hxy
  rcases x with ⟨kx, ix⟩
  rcases y with ⟨ky, iy⟩
  have hi : ix.val = iy.val := congrArg Subtype.val hxy
  have hix := canonicalSelectedPressureCarrier_subset_block n kx.val ix.property
  have hiy := canonicalSelectedPressureCarrier_subset_block n ky.val iy.property
  have hk : kx.val = ky.val := by
    rcases existsUnique_mem_canonicalPaymentBlock n ix.val with ⟨j, _, hu⟩
    exact (hu kx.val hix).trans (hu ky.val (hi ▸ hiy)).symm
  cases kx with
  | mk kx hkx =>
    cases ky with
    | mk ky hky =>
      dsimp only at hk
      subst ky
      cases Subtype.ext hi
      rfl

/-- Block-forgetting embedding into the existing fixed-depth prefix fiber. -/
noncomputable def selectedPressureBucketPrefixEmbedding
    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
    CanonicalSelectedPressureBucketCarrier n q m d ↪
      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
        (paymentEndpointSeq n m + 1) (d + 1)} :=
  ⟨selectedPressureBucketToPrefixFiber hqm,
    selectedPressureBucketToPrefixFiber_injective hqm⟩

/-- Fixed-depth continuation count bounds every selected bucket. -/
theorem natCard_selectedPressureBucket_le_continuationCount
    {n : OddNat} {q m d : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
      orbitDepthContinuationFiberCount n (paymentEndpointSeq n m + 1) (d + 1) := by
  rw [orbitDepthContinuationFiberCount_eq_card_filter_range]
  let e : CanonicalSelectedPressureBucketCarrier n q m d ↪
      {i : ℕ // i ∈ orbitDepthContinuationRangeFiber n
        (paymentEndpointSeq n m + 1) (d + 1)} :=
    selectedPressureBucketPrefixEmbedding hqm
  have hcard := Nat.card_le_card_of_injective e e.injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

/-! ## Exact fixed-depth pressure normal form -/

/-- Exact local pressure: continuation one level deeper, minus the unique
recovery token precisely when the block length equals the queried depth. -/
theorem blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator
    {n : OddNat} {k d : ℕ} (hd : 1 ≤ d) :
    blockPressureContributionInt n k d =
      ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ) -
        if canonicalPaymentBlockLength n k = d then 1 else 0 := by
  rw [blockPressureContributionInt_eq,
    canonicalPaymentBlockContinuationFiber_card]
  by_cases hlt : canonicalPaymentBlockLength n k < d
  · have hsub : canonicalPaymentBlockLength n k - d = 0 :=
      Nat.sub_eq_zero_of_le hlt.le
    have hsubSucc : canonicalPaymentBlockLength n k - (d + 1) = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    simp [hsub, hsubSucc, hlt.ne, Nat.not_le_of_lt hlt]
  by_cases heq : canonicalPaymentBlockLength n k = d
  · simp [heq, hd]
  · have hdl : d < canonicalPaymentBlockLength n k := by omega
    simp [heq, hd, hdl.le]
    omega

/-- Blocks of exact canonical length `d` in the closed interval `q..m`. -/
noncomputable def canonicalExactLengthBlockIndicesAtDepth
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc q m).filter fun k => canonicalPaymentBlockLength n k = d

/-- Fixed-depth pressure summed on a closed canonical block interval. -/
noncomputable def canonicalWindowPressureMarginAtDepth
    (n : OddNat) (q m d : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc q m, blockPressureContributionInt n k d

/-- Exact finite-window fixed-depth normal form. -/
theorem canonicalWindowPressureMarginAtDepth_eq
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    canonicalWindowPressureMarginAtDepth n q m d =
      (∑ k ∈ Finset.Icc q m,
        ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ)) -
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
  classical
  unfold canonicalWindowPressureMarginAtDepth
  simp_rw [blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator hd]
  rw [Finset.sum_sub_distrib]
  simp only [canonicalExactLengthBlockIndicesAtDepth, Finset.sum_boole]

/-! ## Bucket charge versus pressure amplitude -/

/-- All continuation incidences at depth `d + 1` in the closed block window. -/
def CanonicalWindowContinuationCarrierAtDepth
    (n : OddNat) (q m d : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m},
    {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)}

set_option maxHeartbeats 800000 in
-- Elaborating this dependent sigma embedding requires deeper type reduction.
/-- Retaining the block coordinate embeds a selected bucket into the complete
window continuation carrier at the same fixed depth. -/
noncomputable def selectedPressureBucketWindowEmbedding
    (n : OddNat) (q m d : ℕ) :
    CanonicalSelectedPressureBucketCarrier n q m d ↪
      CanonicalWindowContinuationCarrierAtDepth n q m d := by
  let ek : {k : ℕ // k ∈ canonicalSelectedPressureBlocksAtDepth n q m d} ↪
      {k : ℕ // k ∈ Finset.Icc q m} :=
    { toFun := fun k => ⟨k.val,
        (Finset.mem_filter.mp (Finset.mem_filter.mp k.property).1).1⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : {k : ℕ // k ∈ Finset.Icc q m} => z.val) h }
  exact ek.sigmaMap fun k =>
    { toFun := fun i => ⟨i.val,
        CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
          ⟨k, i⟩⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : {i : ℕ // i ∈
          canonicalPaymentBlockContinuationFiber n k.val (d + 1)} => z.val) h }

/-- The window continuation carrier has the expected finite Fubini count. -/
theorem natCard_windowContinuationCarrierAtDepth
    (n : OddNat) (q m d : ℕ) :
    Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) =
      ∑ k ∈ Finset.Icc q m,
        (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
  unfold CanonicalWindowContinuationCarrierAtDepth
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (Finset.Icc q m) fun k =>
    (canonicalPaymentBlockContinuationFiber n k (d + 1)).card

/-- A selected bucket is bounded by exact-length recovery charge plus the
positive part of the fixed-depth pressure margin.  This is finite accounting,
not an allocation to a future boundary. -/
theorem natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
      (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
        Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
  classical
  letI : Fintype {k : ℕ // k ∈ Finset.Icc q m} :=
    Fintype.ofFinset (Finset.Icc q m) (by simp)
  letI (k : {k : ℕ // k ∈ Finset.Icc q m}) :
      Fintype {i : ℕ // i ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)} :=
    Fintype.ofFinset (canonicalPaymentBlockContinuationFiber n k.val (d + 1)) (by simp)
  letI : Fintype (CanonicalWindowContinuationCarrierAtDepth n q m d) := by
    unfold CanonicalWindowContinuationCarrierAtDepth
    infer_instance
  have hbucket :
      Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
        Nat.card (CanonicalWindowContinuationCarrierAtDepth n q m d) :=
    Nat.card_le_card_of_injective (selectedPressureBucketWindowEmbedding n q m d)
      (selectedPressureBucketWindowEmbedding n q m d).injective
  rw [natCard_windowContinuationCarrierAtDepth] at hbucket
  let C := ∑ k ∈ Finset.Icc q m,
    (canonicalPaymentBlockContinuationFiber n k (d + 1)).card
  let E := (canonicalExactLengthBlockIndicesAtDepth n q m d).card
  have hnormal : canonicalWindowPressureMarginAtDepth n q m d = (C : ℤ) - E := by
    simpa [C, E] using canonicalWindowPressureMarginAtDepth_eq (n := n) hd
  by_cases hCE : C ≤ E
  · exact hbucket.trans (by omega)
  · have hEC : E ≤ C := Nat.le_of_lt (Nat.lt_of_not_ge hCE)
    have htoNat : Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) = C - E := by
      rw [hnormal]
      omega
    rw [htoNat]
    exact hbucket.trans (by omega)

/-- Finite existence form of the bucket decomposition. -/
theorem exists_selectedPressureBucketEmbedding_exactLength_add_amplitude
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    Nonempty (CanonicalSelectedPressureBucketCarrier n q m d ↪
      ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
        Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d)))) := by
  classical
  letI : Fintype (CanonicalSelectedPressureBucketCarrier n q m d) := by
    unfold CanonicalSelectedPressureBucketCarrier
    infer_instance
  letI : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
  apply Function.Embedding.nonempty_iff_card_le.mpr
  have htargetCard :
      Fintype.card
          ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
            Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d))) =
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
          Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
    calc
      _ = Fintype.card
            {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} +
          Fintype.card
            (Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d))) :=
        Fintype.card_sum
      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
  rw [htargetCard]
  simpa only [← Nat.card_eq_fintype_card] using
    natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude (n := n) hd

/-- Endpoint-prefix pressure is continuation mass one level deeper minus the
number of exact-length recovery blocks. -/
theorem sourcePressureMarginInt_paymentEndpointSeq_eq_continuation_succ_sub_exactLength
    {n : OddNat} {m d : ℕ} (hd : 1 ≤ d) :
    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d =
      (orbitDepthContinuationFiberCount n
          (paymentEndpointSeq n m + 1) (d + 1) : ℤ) -
        (canonicalExactLengthBlockIndicesAtDepth n 0 m d).card := by
  rw [sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt]
  simp_rw [blockPressureContributionInt_eq_succCarrier_sub_exactLengthIndicator hd]
  rw [Finset.sum_sub_distrib,
    orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum]
  congr 1
  · exact_mod_cast rfl
  · classical
    have hIcc : Finset.Icc 0 m = Finset.range (m + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    simp only [canonicalExactLengthBlockIndicesAtDepth, hIcc, Finset.sum_boole]

end DkMath.Collatz
