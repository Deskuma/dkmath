/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue

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
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  let : Fintype (CanonicalLocalSelectedOrSaturatedCarrier n k) := by
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

/-! ## Active selected buckets and structural Fubini -/

/-- Selected incidences indexed only by positive nonsaturated blocks. -/
def CanonicalActiveSelectedPressureBucketCarrier
    (n : OddNat) (q m d : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d},
    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}

/-- A selected bucket incidence proves that its block is nonsaturated: the
selected carrier of a saturated block is empty. -/
theorem CanonicalSelectedPressureBucketCarrier.block_not_saturated
    {n : OddNat} {q m d : ℕ}
    (x : CanonicalSelectedPressureBucketCarrier n q m d) :
    ¬ CanonicalSaturatedBorderBlock n x.1.val := by
  intro hs
  have hempty := hs.selectedPressureCarrier_eq_empty
  have hi := x.2.property
  simp [hempty] at hi

/-- Removing saturated blocks from a selected bucket loses no incidence. -/
noncomputable def selectedPressureBucketEquivActive
    (n : OddNat) (q m d : ℕ) :
    CanonicalSelectedPressureBucketCarrier n q m d ≃
      CanonicalActiveSelectedPressureBucketCarrier n q m d where
  toFun x := ⟨⟨x.1.val,
    mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
      ⟨mem_canonicalNonsaturatedPositiveBlockIndices.mpr
        ⟨(Finset.mem_filter.mp
            (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1).1,
          (Finset.mem_filter.mp
            (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).1).2,
          x.block_not_saturated⟩,
        (mem_canonicalSelectedPressureBlocksAtDepth.mp x.1.property).2⟩⟩, x.2⟩
  invFun x := ⟨⟨x.1.val, mem_canonicalSelectedPressureBlocksAtDepth.mpr
    ⟨Finset.mem_filter.mpr
      ⟨(mem_canonicalNonsaturatedPositiveBlockIndices.mp
          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).1).1,
        (mem_canonicalNonsaturatedPositiveBlockIndices.mp
          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).1).2.1⟩,
      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.1.property).2⟩⟩, x.2⟩
  left_inv := by
    rintro ⟨k, i⟩
    rfl
  right_inv := by
    rintro ⟨k, i⟩
    rfl

/-- The global selected carrier is structurally the dependent sum of active
depth buckets.  The equivalence preserves both block and source incidence. -/
noncomputable def globalSelectedPressureCarrierEquivActiveBuckets
    (n : OddNat) (q m : ℕ) :
    CanonicalGlobalSelectedPressureCarrier n q m ≃
      Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
        CanonicalActiveSelectedPressureBucketCarrier n q m d.val where
  toFun x := by
    have hnot : ¬ CanonicalSaturatedBorderBlock n x.1.val := by
      intro hs
      have hi := x.2.property
      simp [hs.selectedPressureCarrier_eq_empty] at hi
    have hnonsat : x.1.val ∈ canonicalNonsaturatedPositiveBlockIndices n q m :=
      mem_canonicalNonsaturatedPositiveBlockIndices.mpr
        ⟨(Finset.mem_filter.mp x.1.property).1,
          (Finset.mem_filter.mp x.1.property).2, hnot⟩
    let d := canonicalSelectedPositivePressureDepth n x.1.val
    exact ⟨⟨d, Finset.mem_image.mpr ⟨x.1.val, hnonsat, rfl⟩⟩,
      ⟨⟨x.1.val, mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
        ⟨hnonsat, rfl⟩⟩, x.2⟩⟩
  invFun x := ⟨⟨x.2.1.val,
    Finset.mem_filter.mpr
      ⟨(mem_canonicalNonsaturatedPositiveBlockIndices.mp
          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.2.1.property).1).1,
        (mem_canonicalNonsaturatedPositiveBlockIndices.mp
          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp x.2.1.property).1).2.1⟩⟩,
    x.2.2⟩
  left_inv := by
    rintro ⟨k, i⟩
    rfl
  right_inv := by
    rintro ⟨⟨dv, hdv⟩, ⟨⟨kv, hkv⟩, ⟨iv, hiv⟩⟩⟩
    have heq : canonicalSelectedPositivePressureDepth n kv = dv :=
      (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hkv).2
    subst dv
    rfl

/-! ## Exact-length tokens across active depths -/

/-- Blocks of exact canonical length `d` in the closed interval `q..m`. -/
noncomputable def canonicalExactLengthBlockIndicesAtDepth
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc q m).filter fun k => canonicalPaymentBlockLength n k = d

/-- One exact-length recovery token for each active depth/block match. -/
def CanonicalExactLengthTokenCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
    {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d.val}

/-- Forget depth while retaining the block address.  Injectivity is exactly
uniqueness of the canonical block length. -/
noncomputable def exactLengthTokenBlockEmbedding
    (n : OddNat) (q m : ℕ) :
    CanonicalExactLengthTokenCarrier n q m ↪ {k : ℕ // k ∈ Finset.Icc q m} where
  toFun x := ⟨x.2.val, (Finset.mem_filter.mp x.2.property).1⟩
  inj' := by
    rintro ⟨d, k⟩ ⟨e, l⟩ h
    have hkl : k.val = l.val := congrArg Subtype.val h
    have hd : canonicalPaymentBlockLength n k.val = d.val :=
      (Finset.mem_filter.mp k.property).2
    have he0 : canonicalPaymentBlockLength n l.val = e.val :=
      (Finset.mem_filter.mp l.property).2
    have he : canonicalPaymentBlockLength n k.val = e.val := by
      simpa [hkl] using he0
    have hde : d = e := Subtype.ext (hd.symm.trans he)
    subst e
    have hke : k = l := Subtype.ext hkl
    subst l
    rfl

/-- Exact-length charge over active depths uses at most one token per block. -/
theorem natCard_exactLengthTokenCarrier_le_interval
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalExactLengthTokenCarrier n q m) ≤ m - q + 1 := by
  have hcard := Nat.card_le_card_of_injective
    (exactLengthTokenBlockEmbedding n q m)
    (exactLengthTokenBlockEmbedding n q m).injective
  have hraw : Nat.card (CanonicalExactLengthTokenCarrier n q m) ≤ m + 1 - q := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
      Nat.card_Icc] using hcard
  omega

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

/-- A selected bucket is bounded by exact-length recovery charge plus the
positive part of the fixed-depth pressure margin.  This is finite accounting,
not an allocation to a future boundary. -/
theorem natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
      (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
        Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
  classical
  have hbucket :
      Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) ≤
        ∑ k ∈ Finset.Icc q m,
          (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
    rw [natCard_CanonicalSelectedPressureBucketCarrier]
    calc
      (∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
          (canonicalSelectedPressureCarrier n k).card) =
          ∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
            (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
        apply Finset.sum_congr rfl
        intro k hk
        have hdepth := (mem_canonicalSelectedPressureBlocksAtDepth.mp hk).2
        simp [canonicalSelectedPressureCarrier, hdepth]
      _ ≤ ∑ k ∈ Finset.Icc q m,
          (canonicalPaymentBlockContinuationFiber n k (d + 1)).card := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        exact (Finset.mem_filter.mp
          (mem_canonicalSelectedPressureBlocksAtDepth.mp hk).1).1
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
  let : Fintype (CanonicalSelectedPressureBucketCarrier n q m d) := by
    unfold CanonicalSelectedPressureBucketCarrier
    infer_instance
  let : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
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

/-! ## Minimal selected residual -/

/-- Minimal selected mass left after the available exact-length charge. -/
noncomputable def canonicalSelectedResidualCount
    (n : OddNat) (q m d : ℕ) : ℕ :=
  Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
    (canonicalExactLengthBlockIndicesAtDepth n q m d).card

/-- Exact-length charge plus the minimal residual always covers the active
selected bucket. -/
theorem natCard_activeSelectedBucket_le_exactLength_add_residual
    (n : OddNat) (q m d : ℕ) :
    Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) ≤
      (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
        canonicalSelectedResidualCount n q m d := by
  unfold canonicalSelectedResidualCount
  omega

/-- Accounting embedding into exact-length tokens plus minimal residual units. -/
theorem exists_activeSelectedBucketEmbedding_exactLength_add_residual
    (n : OddNat) (q m d : ℕ) :
    Nonempty (CanonicalActiveSelectedPressureBucketCarrier n q m d ↪
      ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
        Fin (canonicalSelectedResidualCount n q m d))) := by
  classical
  let : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
    unfold CanonicalActiveSelectedPressureBucketCarrier
    infer_instance
  let : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
  apply Function.Embedding.nonempty_iff_card_le.mpr
  have htargetCard :
      Fintype.card
          ({k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ⊕
            Fin (canonicalSelectedResidualCount n q m d)) =
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card +
          canonicalSelectedResidualCount n q m d := by
    calc
      _ = Fintype.card
            {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} +
          Fintype.card (Fin (canonicalSelectedResidualCount n q m d)) :=
        Fintype.card_sum
      _ = _ := by rw [Fintype.card_coe, Fintype.card_fin]
  rw [htargetCard]
  simpa only [← Nat.card_eq_fintype_card] using
    natCard_activeSelectedBucket_le_exactLength_add_residual n q m d

/-- The minimal selected residual is bounded by full fixed-depth pressure
amplitude.  The latter may also contain unselected continuation incidence. -/
theorem selectedResidualCount_le_pressureAmplitude
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    canonicalSelectedResidualCount n q m d ≤
      Int.toNat (canonicalWindowPressureMarginAtDepth n q m d) := by
  have hequivCard :
      Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) =
        Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) :=
    Nat.card_congr (selectedPressureBucketEquivActive n q m d).symm
  have hfull :=
    natCard_selectedPressureBucket_le_exactLength_add_pressureAmplitude
      (n := n) (q := q) (m := m) hd
  unfold canonicalSelectedResidualCount
  rw [hequivCard]
  omega

/-- Residual units embed into the coarser full pressure-amplitude capacity. -/
noncomputable def selectedResidualPressureAmplitudeEmbedding
    {n : OddNat} {q m d : ℕ} (hd : 1 ≤ d) :
    Fin (canonicalSelectedResidualCount n q m d) ↪
      Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d)) :=
  Fin.castLEEmb (selectedResidualCount_le_pressureAmplitude hd)

/-! ## All-depth residual and full-amplitude carriers -/

/-- Minimal selected residual units over active selected depths. -/
def CanonicalSelectedResidualCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
    Fin (canonicalSelectedResidualCount n q m d.val)

/-- Full window pressure-amplitude capacity over active selected depths. -/
def CanonicalPositivePressureAmplitudeCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
    Fin (Int.toNat (canonicalWindowPressureMarginAtDepth n q m d.val))

/-- Assemble the depthwise residual-to-amplitude embeddings. -/
noncomputable def selectedResidualCarrierPressureAmplitudeEmbedding
    (n : OddNat) (q m : ℕ) :
    CanonicalSelectedResidualCarrier n q m ↪
      CanonicalPositivePressureAmplitudeCarrier n q m :=
  (Function.Embedding.refl _).sigmaMap fun d =>
    selectedResidualPressureAmplitudeEmbedding (by
      rcases mem_activeSelectedPressureDepthSupport_iff_nonempty.mp d.property with
        ⟨k, hk⟩
      have hdepth :=
        (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).2
      simpa [hdepth] using one_le_canonicalSelectedPositivePressureDepth n k)

/-- Cardinality of the active-depth bucket sigma. -/
theorem natCard_activeSelectedBuckets
    (n : OddNat) (q m : ℕ) :
    Nat.card
        (Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
        CanonicalActiveSelectedPressureBucketCarrier n q m d.val) =
      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
        Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
  classical
  let (d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m}) :
      Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d.val) := by
    unfold CanonicalActiveSelectedPressureBucketCarrier
    infer_instance
  rw [Nat.card_sigma]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
    fun d => Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d)

/-- Cardinality of all exact-length tokens over active depths. -/
theorem natCard_exactLengthTokenCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalExactLengthTokenCarrier n q m) =
      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
  unfold CanonicalExactLengthTokenCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
    fun d => (canonicalExactLengthBlockIndicesAtDepth n q m d).card

/-- Cardinality of the all-depth minimal residual carrier. -/
theorem natCard_selectedResidualCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalSelectedResidualCarrier n q m) =
      ∑ d ∈ canonicalActiveSelectedPressureDepthSupport n q m,
        canonicalSelectedResidualCount n q m d := by
  unfold CanonicalSelectedResidualCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalActiveSelectedPressureDepthSupport n q m)
    fun d => canonicalSelectedResidualCount n q m d

/-- Primary all-depth reduction: selected incidence is paid first by unique
exact-length block tokens, and only the minimal selected residual remains. -/
theorem natCard_globalSelectedPressureCarrier_le_exactLength_add_residual
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
      Nat.card (CanonicalExactLengthTokenCarrier n q m) +
        Nat.card (CanonicalSelectedResidualCarrier n q m) := by
  rw [Nat.card_congr (globalSelectedPressureCarrierEquivActiveBuckets n q m),
    natCard_activeSelectedBuckets, natCard_exactLengthTokenCarrier,
    natCard_selectedResidualCarrier, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ =>
    natCard_activeSelectedBucket_le_exactLength_add_residual n q m d

/-- Block-count form of the primary residual reduction. -/
theorem natCard_globalSelectedPressureCarrier_le_interval_add_residual
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
      m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m) :=
  (natCard_globalSelectedPressureCarrier_le_exactLength_add_residual n q m).trans
    (Nat.add_le_add_right (natCard_exactLengthTokenCarrier_le_interval hqm) _)

/-- The all-depth minimal residual is bounded by the coarser full-amplitude
capacity.  This follows from an explicit depth-preserving embedding. -/
theorem natCard_selectedResidualCarrier_le_pressureAmplitudeCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalSelectedResidualCarrier n q m) ≤
      Nat.card (CanonicalPositivePressureAmplitudeCarrier n q m) := by
  classical
  let : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  let : Fintype (CanonicalSelectedResidualCarrier n q m) := by
    unfold CanonicalSelectedResidualCarrier
    infer_instance
  let : Fintype (CanonicalPositivePressureAmplitudeCarrier n q m) := by
    unfold CanonicalPositivePressureAmplitudeCarrier
    infer_instance
  exact Nat.card_le_card_of_injective
    (selectedResidualCarrierPressureAmplitudeEmbedding n q m)
    (selectedResidualCarrierPressureAmplitudeEmbedding n q m).injective

/-- Coarser amplitude corollary of the minimal residual reduction. -/
theorem natCard_globalSelectedPressureCarrier_le_interval_add_pressureAmplitude
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) ≤
      m - q + 1 +
        Nat.card (CanonicalPositivePressureAmplitudeCarrier n q m) :=
  (natCard_globalSelectedPressureCarrier_le_interval_add_residual hqm).trans
    (Nat.add_le_add_left
      (natCard_selectedResidualCarrier_le_pressureAmplitudeCarrier n q m) _)

/-- Positive drift reduced to block count, minimal selected residual, and the
already isolated saturated-token packing term. -/
theorem natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_saturated
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
      (m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m)) +
        Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} := by
  exact (natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m).trans
    (Nat.add_le_add_right
      (natCard_globalSelectedPressureCarrier_le_interval_add_residual hqm) _)

/-- Saturated packing yields a completely finite reduction whose only
uncontrolled term is the minimal selected residual carrier. -/
theorem natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_half
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
      (m - q + 1 + Nat.card (CanonicalSelectedResidualCarrier n q m)) +
        (m - q + 2) / 2 := by
  have hsat :
      Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} ≤
        (m - q + 2) / 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      card_canonicalSaturatedBlockIndices_le_half n q m
  exact
    (natCard_positiveDriftUnitCarrier_le_interval_add_residual_add_saturated
      hqm).trans (Nat.add_le_add_left hsat _)

/-! ## Prefix versus sliding-window pressure

The following bridge fixes the endpoint interpretation precisely.  Absolute
source pressure at a canonical block start is the contribution of all earlier
blocks.  Consequently the pressure contributed by blocks `q..m` is the
difference between pressure after block `m` and pressure before block `q`.

This remains a relative increment.  It must not be passed to an API requiring
an absolute `IsSourcePressureDepth` without separately proving the relevant
prefix-pressure hypothesis.
-/

/-- The empty source window has zero pressure at every depth. -/
theorem sourcePressureMarginInt_zero (n : OddNat) (d : ℕ) :
    SourcePressureMarginInt n 0 d = 0 := by
  simp [SourcePressureMarginInt, orbitWindowContinuationSiblingMassPow2,
    orbitWindowRetentionMassPow2]

/-- Pressure at the start of block `q` is the contribution of blocks strictly
before `q`. -/
theorem sourcePressureMarginInt_canonicalBlockStartTime_eq_sum_range
    (n : OddNat) (q d : ℕ) :
    SourcePressureMarginInt n (canonicalBlockStartTime n q) d =
      ∑ k ∈ Finset.range q, blockPressureContributionInt n k d := by
  cases q with
  | zero =>
      simp [canonicalBlockStartTime, canonicalEndpointBlockStart,
        sourcePressureMarginInt_zero]
  | succ q =>
      simpa [canonicalBlockStartTime, canonicalEndpointBlockStart] using
        sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
          n q d

/-- Sliding pressure is the endpoint-prefix pressure minus the pressure already
present at the beginning of the selected block window. -/
theorem canonicalWindowPressureMarginAtDepth_eq_endpoint_sub_start
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) (d : ℕ) :
    canonicalWindowPressureMarginAtDepth n q m d =
      SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d -
        SourcePressureMarginInt n (canonicalBlockStartTime n q) d := by
  have hsubset : Finset.range q ⊆ Finset.range (m + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hIcc : Finset.Icc q m = Finset.range (m + 1) \ Finset.range q := by
    ext i
    simp
    omega
  unfold canonicalWindowPressureMarginAtDepth
  rw [hIcc, Finset.sum_sdiff_eq_sub hsubset,
    ← sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt,
    ← sourcePressureMarginInt_canonicalBlockStartTime_eq_sum_range]

/-- At block zero, sliding pressure recovers the existing endpoint-prefix
pressure theorem exactly. -/
theorem canonicalWindowPressureMarginAtDepth_zero_eq_endpoint
    (n : OddNat) (m d : ℕ) :
    canonicalWindowPressureMarginAtDepth n 0 m d =
      SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d := by
  rw [canonicalWindowPressureMarginAtDepth_eq_endpoint_sub_start n (Nat.zero_le m),
    canonicalBlockStartTime, canonicalEndpointBlockStart,
    sourcePressureMarginInt_zero, sub_zero]

/-! ## Actual canonical block-window carrier -/

/-- The actual source times belonging to canonical blocks `q..m`. -/
noncomputable def canonicalPaymentBlockWindow
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (Finset.Icc q m).biUnion (canonicalPaymentBlock n)

/-- A canonical block is the interval from its proof-independent start time to
its endpoint. -/
theorem canonicalPaymentBlock_eq_Icc_startTime_endpoint
    (n : OddNat) (k : ℕ) :
    canonicalPaymentBlock n k =
      Finset.Icc (canonicalBlockStartTime n k) (paymentEndpointSeq n k) := by
  rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart,
    canonicalBlockStartTime_eq_universalPaymentBlockStart]

/-- The union of consecutive canonical blocks is one closed orbit-time
interval. -/
theorem canonicalPaymentBlockWindow_eq_Icc
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    canonicalPaymentBlockWindow n q m =
      Finset.Icc (canonicalBlockStartTime n q) (paymentEndpointSeq n m) := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_biUnion.mp hi with ⟨k, hk, hik⟩
    rcases Finset.mem_Icc.mp hk with ⟨hqk, hkm⟩
    rw [canonicalPaymentBlock_eq_Icc_startTime_endpoint] at hik
    rcases Finset.mem_Icc.mp hik with ⟨hstart, hend⟩
    apply Finset.mem_Icc.mpr
    constructor
    · cases q with
      | zero =>
          simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
      | succ q =>
          cases k with
          | zero => omega
          | succ k =>
              have he : paymentEndpointSeq n q ≤ paymentEndpointSeq n k :=
                (strictMono_paymentEndpointSeq n).monotone (by omega)
              simpa [canonicalBlockStartTime, canonicalEndpointBlockStart] using
                (Nat.add_le_add_right he 1).trans hstart
    · exact hend.trans ((strictMono_paymentEndpointSeq n).monotone hkm)
  · intro hi
    rcases Finset.mem_Icc.mp hi with ⟨hstartQ, hendM⟩
    rcases existsUnique_mem_canonicalPaymentBlock n i with ⟨k, hik, _⟩
    have hikBounds : canonicalBlockStartTime n k ≤ i ∧
        i ≤ paymentEndpointSeq n k := by
      rw [canonicalPaymentBlock_eq_Icc_startTime_endpoint] at hik
      exact Finset.mem_Icc.mp hik
    have hqk : q ≤ k := by
      by_contra hnot
      have hkq : k < q := Nat.lt_of_not_ge hnot
      cases q with
      | zero => omega
      | succ q =>
          have he : paymentEndpointSeq n k ≤ paymentEndpointSeq n q :=
            (strictMono_paymentEndpointSeq n).monotone (by omega)
          simp [canonicalBlockStartTime, canonicalEndpointBlockStart] at hstartQ
          omega
    have hkm : k ≤ m := by
      by_contra hnot
      have hmk : m < k := Nat.lt_of_not_ge hnot
      cases k with
      | zero => omega
      | succ k =>
          have he : paymentEndpointSeq n m ≤ paymentEndpointSeq n k :=
            (strictMono_paymentEndpointSeq n).monotone (by omega)
          simp [canonicalBlockStartTime, canonicalEndpointBlockStart] at hikBounds
          omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hqk, hkm⟩, hik⟩

/-- Difference-of-prefixes form of the actual block window. -/
theorem canonicalPaymentBlockWindow_eq_range_sdiff
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    canonicalPaymentBlockWindow n q m =
      Finset.range (paymentEndpointSeq n m + 1) \
        Finset.range (canonicalBlockStartTime n q) := by
  rw [canonicalPaymentBlockWindow_eq_Icc n hqm]
  ext i
  simp
  omega

/-- Filtering the actual block window decomposes into the disjoint filtered
canonical blocks retaining their block indices. -/
theorem card_filter_canonicalPaymentBlockWindow_eq_sum
    (n : OddNat) {q m : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    ((canonicalPaymentBlockWindow n q m).filter p).card =
      ∑ k ∈ Finset.Icc q m, ((canonicalPaymentBlock n k).filter p).card := by
  classical
  unfold canonicalPaymentBlockWindow
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion fun k hk l hl hne =>
    (disjoint_canonicalPaymentBlock_of_ne n hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Actual source incidences in the block window continuing beyond depth `d`. -/
noncomputable def canonicalPaymentBlockWindowContinuationFiber
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentBlockWindow n q m).filter fun i =>
    OrbitDepthContinuesBeyond n i d

/-- Actual source incidences in the block window recovering exactly at depth
`d`. -/
noncomputable def canonicalPaymentBlockWindowRecoveryFiber
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentBlockWindow n q m).filter fun i =>
    OrbitDepthRecoversExactlyAt n i d

/-- Sliding continuation incidence decomposes blockwise without losing source
coordinates. -/
theorem card_canonicalPaymentBlockWindowContinuationFiber_eq_sum
    (n : OddNat) (q m d : ℕ) :
    (canonicalPaymentBlockWindowContinuationFiber n q m d).card =
      ∑ k ∈ Finset.Icc q m,
        (canonicalPaymentBlockContinuationFiber n k d).card := by
  classical
  unfold canonicalPaymentBlockWindowContinuationFiber
  unfold canonicalPaymentBlockContinuationFiber
  exact card_filter_canonicalPaymentBlockWindow_eq_sum n _

/-- Sliding exact-recovery incidence decomposes blockwise without losing
source coordinates. -/
theorem card_canonicalPaymentBlockWindowRecoveryFiber_eq_sum
    (n : OddNat) (q m d : ℕ) :
    (canonicalPaymentBlockWindowRecoveryFiber n q m d).card =
      ∑ k ∈ Finset.Icc q m,
        (canonicalPaymentBlockRecoveryFiber n k d).card := by
  classical
  unfold canonicalPaymentBlockWindowRecoveryFiber
  unfold canonicalPaymentBlockRecoveryFiber
  exact card_filter_canonicalPaymentBlockWindow_eq_sum n _

/-- The integer sliding pressure is the signed cardinal balance of the two
actual source-incidence fibers. -/
theorem canonicalWindowPressureMarginAtDepth_eq_actualFiberCard_sub
    (n : OddNat) (q m d : ℕ) :
    canonicalWindowPressureMarginAtDepth n q m d =
      ((canonicalPaymentBlockWindowContinuationFiber n q m d).card : ℤ) -
        (canonicalPaymentBlockWindowRecoveryFiber n q m d).card := by
  rw [card_canonicalPaymentBlockWindowContinuationFiber_eq_sum,
    card_canonicalPaymentBlockWindowRecoveryFiber_eq_sum]
  unfold canonicalWindowPressureMarginAtDepth
  simp_rw [blockPressureContributionInt]
  push_cast
  rw [Finset.sum_sub_distrib]

/-! ## Selected-depth separation from exact-length blocks -/

/-- An active selected depth leaves at least one continuation level after its
selected carrier.  Hence its block length is at least `d + 2`. -/
theorem activeSelectedPressureBlock_depth_add_two_le_length
    {n : OddNat} {q m d k : ℕ}
    (hk : k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d) :
    d + 2 ≤ canonicalPaymentBlockLength n k := by
  have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
  have hnonsat := mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1
  have hcard := endpointAccountingTerm_le_card_selectedPressureCarrier
    hnonsat.2.1 hnonsat.2.2
  have hcardPos : 0 < (canonicalSelectedPressureCarrier n k).card := by
    exact_mod_cast hnonsat.2.1.trans_le hcard
  unfold canonicalSelectedPressureCarrier at hcardPos
  rw [canonicalPaymentBlockContinuationFiber_card, hdata.2] at hcardPos
  omega

/-- Active selected blocks at depth `d` and exact-length blocks at depth `d`
are disjoint.  Exact-length charge therefore always comes from another block. -/
theorem disjoint_activeSelectedPressureBlocks_exactLengthBlocks
    (n : OddNat) (q m d : ℕ) :
    Disjoint (canonicalActiveSelectedPressureBlocksAtDepth n q m d)
      (canonicalExactLengthBlockIndicesAtDepth n q m d) := by
  classical
  rw [Finset.disjoint_left]
  intro k hkActive hkExact
  have hlen := activeSelectedPressureBlock_depth_add_two_le_length hkActive
  have heq := (Finset.mem_filter.mp hkExact).2
  omega

/-! ## Unordered residual terminology -/

/-- Explicit name for the cp-322 cardinal residual.  This natural number has
no source-time or block coordinate and makes no causal matching claim. -/
noncomputable def canonicalUnorderedSelectedCarrierResidualCount
    (n : OddNat) (q m d : ℕ) : ℕ :=
  canonicalSelectedResidualCount n q m d

/-- Exact cardinal-subtraction normal form of the unordered selected residual. -/
theorem canonicalUnorderedSelectedCarrierResidualCount_eq
    (n : OddNat) (q m d : ℕ) :
    canonicalUnorderedSelectedCarrierResidualCount n q m d =
      Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
  rfl

/-- Max-with-zero presentation used when comparing the natural residual with
integer positive-part formulas. -/
theorem canonicalUnorderedSelectedCarrierResidualCount_eq_max_sub_zero
    (n : OddNat) (q m d : ℕ) :
    canonicalUnorderedSelectedCarrierResidualCount n q m d =
      max (Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) -
        (canonicalExactLengthBlockIndicesAtDepth n q m d).card) 0 := by
  simp [canonicalUnorderedSelectedCarrierResidualCount,
    canonicalSelectedResidualCount]

/-! ## Actual selected drift-image carrier -/

/-- Positive nonsaturated drift embeds directly into selected source
incidences of the same block; no saturated summand or cross-block transport is
used. -/
noncomputable def canonicalSelectedPositiveDriftEmbedding
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    Fin (Int.toNat (endpointAccountingTerm n k)) ↪
      {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
  classical
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_fin, Fintype.card_coe]
  have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
      endpointAccountingTerm n k := by
    exact Int.toNat_of_nonneg hpos.le
  omega

/-- The noncanonical finite image of positive drift inside the selected source
carrier.  Its elements still carry the actual source time. -/
noncomputable def canonicalSelectedDriftImageCarrier
    (n : OddNat) (k : ℕ) :
    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
  classical
  by_cases h : 0 < endpointAccountingTerm n k ∧
      ¬ CanonicalSaturatedBorderBlock n k
  · exact Finset.univ.map (canonicalSelectedPositiveDriftEmbedding h.1 h.2)
  · exact ∅

/-- The selected drift image has exactly the positive drift cardinality on a
positive nonsaturated block. -/
theorem card_canonicalSelectedDriftImageCarrier
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    (canonicalSelectedDriftImageCarrier n k).card =
      Int.toNat (endpointAccountingTerm n k) := by
  classical
  simp [canonicalSelectedDriftImageCarrier, hpos, hnot]

/-- Every drift-image element is definitionally a selected source incidence. -/
theorem canonicalSelectedDriftImageCarrier_source_mem
    {n : OddNat} {k : ℕ}
    (x : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k})
    (_hx : x ∈ canonicalSelectedDriftImageCarrier n k) :
    x.val ∈ canonicalSelectedPressureCarrier n k :=
  x.property

/-- Outside the positive nonsaturated branch there is no selected drift
image. -/
theorem canonicalSelectedDriftImageCarrier_eq_empty_of_not_active
    {n : OddNat} {k : ℕ}
    (h : ¬ (0 < endpointAccountingTerm n k ∧
      ¬ CanonicalSaturatedBorderBlock n k)) :
    canonicalSelectedDriftImageCarrier n k = ∅ := by
  classical
  simp [canonicalSelectedDriftImageCarrier, h]

/-! ## Actual spare selected incidences -/

/-- Selected source incidences not used by the chosen same-block drift image. -/
noncomputable def canonicalSelectedDriftSpareCarrier
    (n : OddNat) (k : ℕ) :
    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} := by
  classical
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  exact Finset.univ \ canonicalSelectedDriftImageCarrier n k

/-- The selected source carrier splits exactly into drift image and spare
incidences. -/
theorem card_selectedPressureCarrier_eq_driftImage_add_spare
    (n : OddNat) (k : ℕ) :
    (canonicalSelectedPressureCarrier n k).card =
      (canonicalSelectedDriftImageCarrier n k).card +
        (canonicalSelectedDriftSpareCarrier n k).card := by
  classical
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show canonicalSelectedDriftImageCarrier n k ⊆
      (Finset.univ : Finset {i : ℕ //
        i ∈ canonicalSelectedPressureCarrier n k}) from Finset.subset_univ _)
  rw [Finset.card_univ, Fintype.card_coe] at hsplit
  unfold canonicalSelectedDriftSpareCarrier
  omega

/-- Actual positive-drift images bucketed by selected depth.  The sigma keeps
the block index, while the inner subtype keeps the source time. -/
def CanonicalSelectedDriftBucketCarrier
    (n : OddNat) (q m d : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d},
    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
      i ∈ canonicalSelectedDriftImageCarrier n k.val}

/-! ## Proof-independent fixed-depth arrivals and service -/

/-- Numeric selected-drift arrivals at block `k` and depth `d`.

This definition deliberately does not inspect the classically chosen drift
image.  Choice is used only to realize a source-bearing carrier whose
cardinality is proved below to equal this proof-independent count. -/
noncomputable def canonicalSelectedDriftArrivalCountAtDepth
    (n : OddNat) (k d : ℕ) : ℕ := by
  classical
  exact if 0 < endpointAccountingTerm n k ∧
      ¬ CanonicalSaturatedBorderBlock n k ∧
      canonicalSelectedPositivePressureDepth n k = d
  then Int.toNat (endpointAccountingTerm n k)
  else 0

/-- Local source-bearing drift image restricted to one selected depth. -/
noncomputable def canonicalSelectedDriftImageCarrierAtDepth
    (n : OddNat) (k d : ℕ) :
    Finset {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
  if canonicalSelectedPositivePressureDepth n k = d then
    canonicalSelectedDriftImageCarrier n k
  else ∅

/-- The local depth image realizes exactly the proof-independent arrival
count. -/
theorem card_canonicalSelectedDriftImageCarrierAtDepth
    (n : OddNat) (k d : ℕ) :
    (canonicalSelectedDriftImageCarrierAtDepth n k d).card =
      canonicalSelectedDriftArrivalCountAtDepth n k d := by
  classical
  by_cases hactive : 0 < endpointAccountingTerm n k ∧
      ¬ CanonicalSaturatedBorderBlock n k
  · by_cases hdepth : canonicalSelectedPositivePressureDepth n k = d
    · simp [canonicalSelectedDriftImageCarrierAtDepth,
        canonicalSelectedDriftArrivalCountAtDepth, hactive, hdepth,
        card_canonicalSelectedDriftImageCarrier]
    · simp [canonicalSelectedDriftImageCarrierAtDepth,
        canonicalSelectedDriftArrivalCountAtDepth, hdepth]
  · have hempty := canonicalSelectedDriftImageCarrier_eq_empty_of_not_active hactive
    by_cases hdepth : canonicalSelectedPositivePressureDepth n k = d
    · rw [show canonicalSelectedDriftImageCarrierAtDepth n k d =
          canonicalSelectedDriftImageCarrier n k by
          simp [canonicalSelectedDriftImageCarrierAtDepth, hdepth], hempty]
      rw [Finset.card_empty]
      unfold canonicalSelectedDriftArrivalCountAtDepth
      split_ifs with hfull
      · exact (hactive ⟨hfull.1, hfull.2.1⟩).elim
      · rfl
    · simp [canonicalSelectedDriftImageCarrierAtDepth,
        canonicalSelectedDriftArrivalCountAtDepth, hdepth]

/-- Cardinality of the selected drift bucket is the sum of its
proof-independent per-block arrivals over the closed block window. -/
theorem natCard_CanonicalSelectedDriftBucketCarrier_eq_sum_arrivals
    (n : OddNat) (q m d : ℕ) :
    Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) =
      ∑ k ∈ Finset.Icc q m,
        canonicalSelectedDriftArrivalCountAtDepth n k d := by
  classical
  unfold CanonicalSelectedDriftBucketCarrier
  rw [Nat.card_sigma, Finset.univ_eq_attach]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.sum_attach
    (canonicalActiveSelectedPressureBlocksAtDepth n q m d)
    (fun k => (canonicalSelectedDriftImageCarrier n k).card)]
  calc
    (∑ k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d,
        (canonicalSelectedDriftImageCarrier n k).card) =
        ∑ k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d,
          canonicalSelectedDriftArrivalCountAtDepth n k d := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdata := mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk
      have hnonsat := mem_canonicalNonsaturatedPositiveBlockIndices.mp hdata.1
      rw [card_canonicalSelectedDriftImageCarrier hnonsat.2.1 hnonsat.2.2]
      simp [canonicalSelectedDriftArrivalCountAtDepth, hnonsat.2.1,
        hnonsat.2.2, hdata.2]
    _ = ∑ k ∈ Finset.Icc q m,
          canonicalSelectedDriftArrivalCountAtDepth n k d := by
      apply Finset.sum_subset
      · intro k hk
        exact (mem_canonicalNonsaturatedPositiveBlockIndices.mp
          (mem_canonicalActiveSelectedPressureBlocksAtDepth.mp hk).1).1
      · intro k hkIcc hkNotActive
        have hinactive : ¬ (0 < endpointAccountingTerm n k ∧
            ¬ CanonicalSaturatedBorderBlock n k ∧
            canonicalSelectedPositivePressureDepth n k = d) := by
          intro h
          exact hkNotActive (mem_canonicalActiveSelectedPressureBlocksAtDepth.mpr
            ⟨mem_canonicalNonsaturatedPositiveBlockIndices.mpr
              ⟨hkIcc, h.1, h.2.1⟩, h.2.2⟩)
        simp [canonicalSelectedDriftArrivalCountAtDepth, hinactive]

/-- One exact-length service token is available precisely at a block whose
canonical length equals `d`. -/
noncomputable def canonicalExactLengthServiceAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  if canonicalPaymentBlockLength n k = d then 1 else 0

/-- Total exact-length service is the cardinality of the existing exact-length
block index carrier. -/
theorem sum_canonicalExactLengthServiceAtDepth_eq_card
    (n : OddNat) (q m d : ℕ) :
    (∑ k ∈ Finset.Icc q m, canonicalExactLengthServiceAtDepth n k d) =
      (canonicalExactLengthBlockIndicesAtDepth n q m d).card := by
  classical
  simp [canonicalExactLengthServiceAtDepth,
    canonicalExactLengthBlockIndicesAtDepth, Finset.sum_boole]

/-! ## Fixed-depth causal queue -/

/-- Causal reflected queue for actual selected-drift arrivals at depth `d`
against one exact-length service token per qualifying block. -/
noncomputable def canonicalSelectedDriftDepthQueue
    (n : OddNat) (q m d : ℕ) : ℕ :=
  finiteReflectedQueueOn
    (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
    (fun k => canonicalExactLengthServiceAtDepth n k d) q m

/-- Lindley maximum form of the fixed-depth causal queue. -/
theorem canonicalSelectedDriftDepthQueue_eq_windowMaximum
    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
    canonicalSelectedDriftDepthQueue n q m d =
      finiteReflectedWindowMaximum
        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
  exact finiteReflectedQueueOn_eq_windowMaximum _ _ hqm

/-! ## Source-bearing temporal matching -/

/-- Actual selected drift-image incidences in the full block window.  The
outer coordinate is the release block and the inner subtype retains the
original source time.  Inactive fibers are empty. -/
def CanonicalSelectedDriftArrivalWindowCarrier
    (n : OddNat) (q m d : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m},
    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
      i ∈ canonicalSelectedDriftImageCarrierAtDepth n k.val d}

/-- A source-bearing causal matching sends every actual selected-drift
incidence to a distinct exact-length service token at its release block or a
later block. -/
def CanonicalSelectedDriftForwardWindowMatching
    (n : OddNat) (q m d : ℕ) : Prop :=
  q ≤ m ∧ ∃ pay : CanonicalSelectedDriftArrivalWindowCarrier n q m d →
      FiniteServiceWindowCarrier
        (fun k => canonicalExactLengthServiceAtDepth n k d) q m,
    Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val

/-- Each source-bearing local drift-image fiber is block-preservingly
equivalent to the proof-independent numeric arrival fiber. -/
noncomputable def canonicalSelectedDriftArrivalFiberEquiv
    (n : OddNat) (k d : ℕ) :
    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
      i ∈ canonicalSelectedDriftImageCarrierAtDepth n k d} ≃
      Fin (canonicalSelectedDriftArrivalCountAtDepth n k d) := by
  classical
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  let : Fintype
      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
        i ∈ canonicalSelectedDriftImageCarrierAtDepth n k d} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrierAtDepth n k d) (by simp)
  apply Fintype.equivOfCardEq
  rw [Fintype.card_coe, Fintype.card_fin,
    card_canonicalSelectedDriftImageCarrierAtDepth]

/-- Block-preserving equivalence between actual source arrivals and the
generic numeric arrival carrier. -/
noncomputable def canonicalSelectedDriftArrivalWindowEquiv
    (n : OddNat) (q m d : ℕ) :
    CanonicalSelectedDriftArrivalWindowCarrier n q m d ≃
      FiniteArrivalWindowCarrier
        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d) q m :=
  Equiv.sigmaCongrRight fun k =>
    canonicalSelectedDriftArrivalFiberEquiv n k.val d

/-- The source-bearing temporal matching is exactly the generic interval-order
matching after a block-preserving change of arrival fiber coordinates. -/
theorem canonicalSelectedDriftForwardWindowMatching_iff_finiteForward
    (n : OddNat) (q m d : ℕ) :
    CanonicalSelectedDriftForwardWindowMatching n q m d ↔
      FiniteForwardWindowMatching
        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
  classical
  let e := canonicalSelectedDriftArrivalWindowEquiv n q m d
  constructor
  · rintro ⟨hqm, pay, hinj, hforward⟩
    refine ⟨hqm, fun claim => pay (e.symm claim), ?_, ?_⟩
    · exact hinj.comp e.symm.injective
    · intro claim
      have hfst : (e.symm claim).fst = claim.fst := by
        rfl
      simpa [hfst] using hforward (e.symm claim)
  · rintro ⟨hqm, pay, hinj, hforward⟩
    refine ⟨hqm, fun claim => pay (e claim), ?_, ?_⟩
    · exact hinj.comp e.injective
    · intro claim
      have hfst : (e claim).fst = claim.fst := by
        rfl
      simpa [hfst] using hforward (e claim)

/-- Fixed-depth queue zero is equivalent to a forward matching that retains
the actual claim source coordinate. -/
theorem canonicalSelectedDriftDepthQueue_eq_zero_iff_sourceMatching
    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
    canonicalSelectedDriftDepthQueue n q m d = 0 ↔
      CanonicalSelectedDriftForwardWindowMatching n q m d := by
  rw [canonicalSelectedDriftForwardWindowMatching_iff_finiteForward]
  exact finiteReflectedQueueOn_eq_zero_iff_forwardWindowMatching _ _ hqm

/-- Forgetting image membership embeds the actual drift bucket into the full
active selected bucket without changing block or source coordinates. -/
def selectedDriftBucketActiveSelectedEmbedding
    (n : OddNat) (q m d : ℕ) :
    CanonicalSelectedDriftBucketCarrier n q m d ↪
      CanonicalActiveSelectedPressureBucketCarrier n q m d :=
  (Function.Embedding.refl _).sigmaMap fun _ =>
    { toFun := fun x => x.val
      inj' := Subtype.val_injective }

/-- Unordered residual of actual positive-drift images after granting all
same-depth exact-length tokens. -/
noncomputable def canonicalUnorderedSelectedDriftResidualCount
    (n : OddNat) (q m d : ℕ) : ℕ :=
  Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) -
    (canonicalExactLengthBlockIndicesAtDepth n q m d).card

/-- The old unordered cardinal subtraction is exactly the generic positive
part of total fixed-depth signed balance. -/
theorem canonicalUnorderedSelectedDriftResidualCount_eq_finiteUnorderedResidual
    (n : OddNat) (q m d : ℕ) :
    canonicalUnorderedSelectedDriftResidualCount n q m d =
      finiteUnorderedResidual
        (fun k => canonicalSelectedDriftArrivalCountAtDepth n k d)
        (fun k => canonicalExactLengthServiceAtDepth n k d) q m := by
  rw [canonicalUnorderedSelectedDriftResidualCount,
    natCard_CanonicalSelectedDriftBucketCarrier_eq_sum_arrivals,
    ← sum_canonicalExactLengthServiceAtDepth_eq_card]
  unfold finiteUnorderedResidual finiteSignedWindowBalance
  rw [Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  omega

/-- The unordered actual drift residual is bounded by the causal reflected
queue.  This compares cardinalities only and does not reinterpret the chosen
unordered residual carrier as a causal state. -/
theorem canonicalUnorderedSelectedDriftResidualCount_le_depthQueue
    (n : OddNat) {q m d : ℕ} (hqm : q ≤ m) :
    canonicalUnorderedSelectedDriftResidualCount n q m d ≤
      canonicalSelectedDriftDepthQueue n q m d := by
  rw [canonicalUnorderedSelectedDriftResidualCount_eq_finiteUnorderedResidual]
  exact finiteUnorderedResidual_le_reflectedQueueOn _ _ hqm

/-- The actual drift residual is bounded by the cp-322 selected-carrier
residual.  The difference is precisely unused selected-carrier slack. -/
theorem unorderedSelectedDriftResidualCount_le_selectedCarrierResidualCount
    (n : OddNat) (q m d : ℕ) :
    canonicalUnorderedSelectedDriftResidualCount n q m d ≤
      canonicalUnorderedSelectedCarrierResidualCount n q m d := by
  classical
  let : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  let : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  let : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
    unfold CanonicalActiveSelectedPressureBucketCarrier
    infer_instance
  have hcard :
      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d) ≤
        Nat.card (CanonicalActiveSelectedPressureBucketCarrier n q m d) :=
    Nat.card_le_card_of_injective
      (selectedDriftBucketActiveSelectedEmbedding n q m d)
      (selectedDriftBucketActiveSelectedEmbedding n q m d).injective
  unfold canonicalUnorderedSelectedDriftResidualCount
  unfold canonicalUnorderedSelectedCarrierResidualCount
  unfold canonicalSelectedResidualCount
  omega

/-! ## Noncanonical actual residual incidence carrier -/

/-- When enough actual drift-image incidences exist, choose an unordered
injection of exact-length tokens into them.  This choice has no temporal
meaning. -/
noncomputable def canonicalExactLengthToDriftBucketEmbedding
    {n : OddNat} {q m d : ℕ}
    (hcard : (canonicalExactLengthBlockIndicesAtDepth n q m d).card ≤
      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d)) :
    {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} ↪
      CanonicalSelectedDriftBucketCarrier n q m d := by
  classical
  let : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  let : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  let : Fintype
      {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_coe]
  simpa only [Nat.card_eq_fintype_card] using hcard

/-- Actual unmatched drift-image incidences after a noncanonical unordered
matching with exact-length tokens. -/
noncomputable def canonicalActualSelectedDriftResidualFinset
    (n : OddNat) (q m d : ℕ) :
    Finset (CanonicalSelectedDriftBucketCarrier n q m d) := by
  classical
  let : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  let : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  by_cases hcard : (canonicalExactLengthBlockIndicesAtDepth n q m d).card ≤
      Nat.card (CanonicalSelectedDriftBucketCarrier n q m d)
  · exact Finset.univ \ Finset.univ.map
      (canonicalExactLengthToDriftBucketEmbedding hcard)
  · exact ∅

/-- Source-bearing subtype of the chosen unmatched drift incidences. -/
def CanonicalActualSelectedDriftResidualCarrier
    (n : OddNat) (q m d : ℕ) :=
  {x : CanonicalSelectedDriftBucketCarrier n q m d //
    x ∈ canonicalActualSelectedDriftResidualFinset n q m d}

/-- The actual residual carrier is a subtype of the drift-image bucket. -/
def actualSelectedDriftResidualCarrierEmbedding
    (n : OddNat) (q m d : ℕ) :
    CanonicalActualSelectedDriftResidualCarrier n q m d ↪
      CanonicalSelectedDriftBucketCarrier n q m d :=
  Function.Embedding.subtype _

/-- The chosen actual residual has exactly the unordered drift-residual
cardinality. -/
theorem natCard_actualSelectedDriftResidualCarrier
    (n : OddNat) (q m d : ℕ) :
    Nat.card (CanonicalActualSelectedDriftResidualCarrier n q m d) =
      canonicalUnorderedSelectedDriftResidualCount n q m d := by
  classical
  let : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  let (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  let : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  let : Fintype
      {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
  let : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d) (by simp)
  rw [Nat.card_eq_fintype_card]
  unfold CanonicalActualSelectedDriftResidualCarrier
  rw [Fintype.card_coe]
  unfold canonicalActualSelectedDriftResidualFinset
  split_ifs with hcard
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_map, Finset.card_univ]
    simp only [canonicalUnorderedSelectedDriftResidualCount,
      Nat.card_eq_fintype_card, Fintype.card_coe]
  · simp only [Finset.card_empty, canonicalUnorderedSelectedDriftResidualCount]
    omega

/-! ## All-depth causal carrier -/

/-- All actual unordered residual incidences, separated by active selected
depth.  This is only a disjoint depthwise package; it does not share service
tokens across depths. -/
def CanonicalAllDepthActualSelectedDriftResidualCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
    CanonicalActualSelectedDriftResidualCarrier n q m d.val

/-- Abstract causal outstanding capacity at every active selected depth. -/
def CanonicalAllDepthSelectedDriftCausalQueueCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m},
    Fin (canonicalSelectedDriftDepthQueue n q m d.val)

/-- Every depthwise unordered residual cardinality is bounded by its causal
queue, hence the same is true after taking their disjoint sigma sum. -/
theorem natCard_allDepthActualResidual_le_causalQueueCarrier
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    Nat.card (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) ≤
      Nat.card (CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
  classical
  let : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  let (d : {d : ℕ // d ∈
      canonicalActiveSelectedPressureDepthSupport n q m}) :
      Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d.val) :=
    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d.val) (by simp)
  unfold CanonicalAllDepthActualSelectedDriftResidualCarrier
  unfold CanonicalAllDepthSelectedDriftCausalQueueCarrier
  rw [Nat.card_sigma, Nat.card_sigma]
  apply Finset.sum_le_sum
  intro d hd
  rw [natCard_actualSelectedDriftResidualCarrier, Nat.card_fin]
  exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue n hqm

/-- Explicit depthwise embedding of actual residual incidences into the
corresponding causal queue fiber. -/
noncomputable def actualSelectedDriftResidualDepthEmbedding
    (n : OddNat) {q m : ℕ} (d : ℕ) (hqm : q ≤ m) :
    CanonicalActualSelectedDriftResidualCarrier n q m d ↪
      Fin (canonicalSelectedDriftDepthQueue n q m d) := by
  classical
  let : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
    natCard_actualSelectedDriftResidualCarrier]
  exact canonicalUnorderedSelectedDriftResidualCount_le_depthQueue n hqm

/-- Depth-preserving all-depth embedding.  No service token is converted or
shared between depth fibers. -/
noncomputable def allDepthActualResidualCausalQueueEmbedding
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    CanonicalAllDepthActualSelectedDriftResidualCarrier n q m ↪
      CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m :=
  (Function.Embedding.refl _).sigmaMap fun d => by
    exact actualSelectedDriftResidualDepthEmbedding n d.val hqm

/-- The explicit all-depth embedding preserves the depth coordinate
definitionally. -/
@[simp] theorem allDepthActualResidualCausalQueueEmbedding_fst
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
    (x : CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) :
    (allDepthActualResidualCausalQueueEmbedding n hqm x).1 = x.1 :=
  rfl

/-- Noncanonical finite embedding witnessing the all-depth cardinal
comparison.  Its target fibers remain depth-separated. -/
theorem exists_allDepthActualResidualEmbedding_causalQueueCarrier
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    Nonempty (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m ↪
      CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
  classical
  let : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  let (d : {d : ℕ // d ∈
      canonicalActiveSelectedPressureDepthSupport n q m}) :
      Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d.val) :=
    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d.val) (by simp)
  let : Fintype (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) := by
    unfold CanonicalAllDepthActualSelectedDriftResidualCarrier
    infer_instance
  let : Fintype (CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
    unfold CanonicalAllDepthSelectedDriftCausalQueueCarrier
    infer_instance
  apply Function.Embedding.nonempty_iff_card_le.mpr
  simpa only [Nat.card_eq_fintype_card] using
    natCard_allDepthActualResidual_le_causalQueueCarrier n hqm

/-! ## Spare selected incidence on nonsaturated blocks -/

/-- A positive nonsaturated block of terminal valuation at least two has one
selected incidence beyond its positive drift image.  This is the local slack
needed for a future charge of an immediately preceding saturated token; no
such cross-block charge is asserted here. -/
theorem intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    Int.toNat (endpointAccountingTerm n k) + 1 ≤
      (canonicalSelectedPressureCarrier n k).card := by
  have hclaimsLe := canonicalBlockClaimCount_le_length n k
  have hclaimsLt : canonicalBlockClaimCount n k < canonicalBlockLength n k := by
    by_contra h
    have heq : canonicalBlockClaimCount n k = canonicalBlockLength n k := by omega
    exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length hpos heq)
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
  have htoNat : Int.toNat (endpointAccountingTerm n k) =
      canonicalBlockClaimCount n k - canonicalBlockTerminalValuation n k := by
    have hnonneg : 0 ≤ endpointAccountingTerm n k := hpos.le
    have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
        endpointAccountingTerm n k := Int.toNat_of_nonneg hnonneg
    exact_mod_cast (show (Int.toNat (endpointAccountingTerm n k) : ℤ) =
      (canonicalBlockClaimCount n k -
        canonicalBlockTerminalValuation n k : ℕ) by omega)
  unfold canonicalSelectedPressureCarrier
  rw [canonicalPaymentBlockContinuationFiber_card]
  rw [canonicalSelectedPositivePressureDepth, if_neg (by omega)]
  rw [htoNat]
  change canonicalBlockClaimCount n k - canonicalBlockTerminalValuation n k + 1 ≤
    canonicalBlockLength n k -
      (canonicalBlockTerminalValuation n k - 1 + 1)
  have hvlt :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  omega

/-- Terminal valuation at least two forces an actual spare selected source
incidence on every positive nonsaturated block. -/
theorem canonicalSelectedDriftSpareCarrier_nonempty
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    (canonicalSelectedDriftSpareCarrier n k).Nonempty := by
  apply Finset.card_pos.mp
  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
  have hslack :=
    intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card
      hpos hnot hv
  omega

/-- One explicit unit embeds into the actual spare selected-incidence subtype. -/
noncomputable def oneEmbedding_canonicalSelectedDriftSpareCarrier
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    Fin 1 ↪ {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
      i ∈ canonicalSelectedDriftSpareCarrier n k} := by
  classical
  let : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  let : Fintype
      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
        i ∈ canonicalSelectedDriftSpareCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n k) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_fin, Fintype.card_coe]
  exact Finset.one_le_card.mpr
    (canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv)

/-! ## Exact no-spare classes -/

/-! ### Claim-hole accounting normal form -/

/-- The deepest block depth is exactly the block's start time. -/
theorem canonicalPaymentSourceAtDepth_length_eq_startTime
    (n : OddNat) (k : ℕ) :
    canonicalPaymentSourceAtDepth n k (canonicalBlockLength n k) =
      canonicalBlockStartTime n k := by
  unfold canonicalPaymentSourceAtDepth
  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
  have hL := one_le_canonicalBlockLength n k
  omega

/--
Exact state at a valid block depth.  Depth counts backwards from the endpoint,
so the dyadic exponent is `d` while the ternary exponent is `L - d`.
-/
theorem canonicalPaymentSourceAtDepth_iterate_add_one_eq
    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
    (hdL : d ≤ canonicalBlockLength n k) :
    (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 + 1 =
      2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
        canonicalBlockOddCore n k := by
  let L := canonicalBlockLength n k
  let t := L - d
  have ht : t < L := by omega
  have htd : t + d = L := by omega
  have hsource : canonicalPaymentSourceAtDepth n k d =
      canonicalBlockStartTime n k + t := by
    unfold canonicalPaymentSourceAtDepth
    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
    dsimp [L, t]
    omega
  have hnormal :=
    canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore n k t (by
      simpa [L] using ht)
  rw [← hsource] at hnormal
  have hpow : 2 ^ canonicalBlockLength n k = 2 ^ t * 2 ^ d := by
    have htd' : t + d = canonicalBlockLength n k := by
      simpa [L] using htd
    rw [← htd']
    exact pow_add 2 t d
  rw [hpow] at hnormal
  have hcancel :
      2 ^ t * ((iterateT (canonicalPaymentSourceAtDepth n k d) n).1 + 1) =
        2 ^ t * (2 ^ d * 3 ^ t * canonicalBlockOddCore n k) := by
    calc
      _ = 3 ^ t * (2 ^ t * 2 ^ d * canonicalBlockOddCore n k) := hnormal
      _ = 2 ^ t * (2 ^ d * 3 ^ t * canonicalBlockOddCore n k) := by ring
  have htpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  have hresult := Nat.eq_of_mul_eq_mul_left htpos hcancel
  simpa [L, t] using hresult

/-- Generic claim-profile transport in block-core coordinates. -/
theorem mem_canonicalPaymentClaimDepths_iff_stateUpperCarry_coreWord
    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
    (hdL : d ≤ canonicalBlockLength n k) :
    d ∈ canonicalPaymentClaimDepths n k ↔
      stateUpperCarry
        (2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
          canonicalBlockOddCore n k - 1) = 2 := by
  rw [mem_canonicalPaymentClaimDepths_iff]
  have hform := canonicalPaymentSourceAtDepth_iterate_add_one_eq
    n k d hd1 hdL
  have hstate :
      (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 =
        2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
          canonicalBlockOddCore n k - 1 := by
    omega
  have hdL' : d ≤ canonicalPaymentBlockLength n k := by
    simpa [canonicalBlockLength] using hdL
  constructor
  · rintro ⟨_, _, hcarry⟩
    unfold CarryTwoDebtAt at hcarry
    simpa [hstate] using hcarry
  · intro hcarry
    refine ⟨hd1, hdL', ?_⟩
    unfold CarryTwoDebtAt
    simpa [hstate] using hcarry

/-- Exact block-core word observed at positive depth `d`. -/
noncomputable def canonicalBlockCoreWordAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
    canonicalBlockOddCore n k - 1

/-- Caller-facing form of the exact source-state formula. -/
theorem iterateT_sourceAtDepth_eq_coreWordAtDepth
    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
    (hdL : d ≤ canonicalBlockLength n k) :
    (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 =
      canonicalBlockCoreWordAtDepth n k d := by
  unfold canonicalBlockCoreWordAtDepth
  have h := canonicalPaymentSourceAtDepth_iterate_add_one_eq n k d hd1 hdL
  omega

/-- Caller-facing claim test through the exact block-core word. -/
theorem mem_claimDepths_iff_coreWordAtDepth_carryTwo
    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
    (hdL : d ≤ canonicalBlockLength n k) :
    d ∈ canonicalPaymentClaimDepths n k ↔
      stateUpperCarry (canonicalBlockCoreWordAtDepth n k d) = 2 := by
  simpa [canonicalBlockCoreWordAtDepth] using
    mem_canonicalPaymentClaimDepths_iff_stateUpperCarry_coreWord n k d hd1 hdL

/-- Adjacent core words satisfy the exact internal `3:2` recurrence. -/
theorem canonicalBlockCoreWordAtDepth_succ_recurrence
    (n : OddNat) (k d : ℕ) (_hd1 : 1 ≤ d)
    (hdL : d < canonicalBlockLength n k) :
    3 * (canonicalBlockCoreWordAtDepth n k (d + 1) + 1) =
      2 * (canonicalBlockCoreWordAtDepth n k d + 1) := by
  unfold canonicalBlockCoreWordAtDepth
  have hu := canonicalBlockOddCore_pos n k
  have hpow : canonicalBlockLength n k - d =
      (canonicalBlockLength n k - (d + 1)) + 1 := by omega
  rw [hpow, pow_succ]
  rw [pow_succ]
  have hposS : 0 < 2 ^ d * 2 *
      3 ^ (canonicalBlockLength n k - (d + 1)) *
        canonicalBlockOddCore n k := by positivity
  have hposD : 0 < 2 ^ d *
      (3 ^ (canonicalBlockLength n k - (d + 1)) * 3) *
        canonicalBlockOddCore n k := by positivity
  rw [Nat.sub_add_cancel hposS, Nat.sub_add_cancel hposD]
  ring

/-- Increasing depth by one walks one source-time step backwards. -/
theorem canonicalPaymentSourceAtDepth_succ_add_one
    (n : OddNat) (k d : ℕ) (_hd1 : 1 ≤ d)
    (hdL : d < canonicalBlockLength n k) :
    canonicalPaymentSourceAtDepth n k (d + 1) + 1 =
      canonicalPaymentSourceAtDepth n k d := by
  unfold canonicalPaymentSourceAtDepth
  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
  omega

/--
The exact adjacent recurrence alone does not make carry profiles monotone.
The words `53, 35, 23` satisfy the same consecutive `3:2` recurrence while
their own-width carries alternate `2, 1, 2`.  Additional canonical-block
information is therefore required for any claim-hole density theorem.
-/
theorem coreWordRecurrence_carry_alternation_witness :
    3 * (35 + 1) = 2 * (53 + 1) ∧
      3 * (23 + 1) = 2 * (35 + 1) ∧
        stateUpperCarry 53 = 2 ∧
          stateUpperCarry 35 = 1 ∧
            stateUpperCarry 23 = 2 := by
  norm_num [stateUpperCarry, upperCarry3n1, bitWidth]

/-! ## Canonical carry-alternation regression -/

/-- Odd root whose first canonical block realizes the `53,35,23` profile. -/
def twentyThreeCarryAlternationOdd : OddNat := ⟨23, by norm_num⟩

private lemma twentyThree_v2_24 : v2 24 = 3 := by
  have h12 := (DkMath.ABC.padic_val_two_of_even 12).2 (by decide)
  have h6 := (DkMath.ABC.padic_val_two_of_even 6).2 (by decide)
  have h3 := (DkMath.ABC.padic_val_two_of_even 3).2 (by decide)
  have hv3 : v2 3 = 0 := v2_odd 3 (by decide)
  have hv6 : v2 6 = 1 := by simpa [v2, hv3] using h3
  have hv12 : v2 12 = 2 := by simpa [v2, hv6] using h6
  simpa [v2, hv12] using h12

private theorem twentyThree_endpoint_zero :
    paymentEndpointSeq twentyThreeCarryAlternationOdd 0 = 2 := by
  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
    ResidualAllOnesDepth, oddOrbitLabel, iterateT,
    twentyThreeCarryAlternationOdd, mkOddNat, twentyThree_v2_24]

private theorem twentyThree_paymentBlockLength_zero :
    canonicalPaymentBlockLength twentyThreeCarryAlternationOdd 0 = 3 := by
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
    universalPaymentBlockStart_paymentEndpointSeq_zero,
    twentyThree_endpoint_zero]

/-- The first canonical block at odd root `23` has length three. -/
theorem canonicalBlockLength_twentyThree_zero :
    canonicalBlockLength twentyThreeCarryAlternationOdd 0 = 3 :=
  twentyThree_paymentBlockLength_zero

private theorem canonicalBlockStartState_twentyThree_zero :
    canonicalBlockStartState twentyThreeCarryAlternationOdd 0 = 23 := by
  unfold canonicalBlockStartState canonicalBlockStartTime canonicalEndpointBlockStart
  rfl

/-- The first canonical block at odd root `23` has odd core three. -/
theorem canonicalBlockOddCore_twentyThree_zero :
    canonicalBlockOddCore twentyThreeCarryAlternationOdd 0 = 3 := by
  rw [canonicalBlockOddCore, canonicalBlockStartState_twentyThree_zero,
    canonicalBlockLength_twentyThree_zero]
  norm_num

/-- Exact three-word core profile of the first canonical block at `23`. -/
theorem canonicalBlockCoreWords_twentyThree_zero :
    canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 1 = 53 ∧
      canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 2 = 35 ∧
        canonicalBlockCoreWordAtDepth twentyThreeCarryAlternationOdd 0 3 = 23 := by
  simp [canonicalBlockCoreWordAtDepth, canonicalBlockLength_twentyThree_zero,
    canonicalBlockOddCore_twentyThree_zero]

private lemma twentyThree_v2_70 : v2 70 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 35).2 (by decide)
  simpa [v2, v2_odd 35 (by decide)] using h

private lemma twentyThree_v2_106 : v2 106 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 53).2 (by decide)
  simpa [v2, v2_odd 53 (by decide)] using h

private theorem twentyThree_carry_zero :
    CarryTwoDebtAt twentyThreeCarryAlternationOdd 0 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, twentyThreeCarryAlternationOdd, mkOddNat]

private theorem twentyThree_not_carry_one :
    ¬ CarryTwoDebtAt twentyThreeCarryAlternationOdd 1 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, twentyThreeCarryAlternationOdd, mkOddNat, threeNPlusOne,
    pow2, twentyThree_v2_70]

private theorem twentyThree_carry_two :
    CarryTwoDebtAt twentyThreeCarryAlternationOdd 2 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, twentyThreeCarryAlternationOdd, mkOddNat, threeNPlusOne,
    pow2, twentyThree_v2_70, twentyThree_v2_106]

/-- The canonical carry profile at `23` claims depths one and three. -/
theorem canonicalPaymentClaimDepths_twentyThree_zero :
    canonicalPaymentClaimDepths twentyThreeCarryAlternationOdd 0 = {1, 3} := by
  classical
  ext d
  rw [mem_canonicalPaymentClaimDepths_iff,
    twentyThree_paymentBlockLength_zero]
  unfold canonicalPaymentSourceAtDepth
  rw [twentyThree_endpoint_zero]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd1, hd3, hcarry⟩
    interval_cases d <;>
      simp_all [twentyThree_carry_zero, twentyThree_not_carry_one]
  · rintro (rfl | rfl) <;>
      simp [twentyThree_carry_zero, twentyThree_carry_two]

/-!
This canonical regression proves only that adjacent recurrence does not imply
monotone carry.  It does not rule out bounded-gap or density theorems that use
the canonical residue class, odd core, or block width.
-/

/-- Positive depths in the block which do not carry a canonical payment
claim. -/
noncomputable def canonicalBlockClaimHoles
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.Icc 1 (canonicalBlockLength n k) \
    canonicalPaymentClaimDepths n k

/-- The unique hole in the canonical carry profile at `23` is depth two. -/
theorem canonicalBlockClaimHoles_twentyThree_zero :
    canonicalBlockClaimHoles twentyThreeCarryAlternationOdd 0 = {2} := by
  classical
  rw [canonicalBlockClaimHoles, canonicalBlockLength_twentyThree_zero,
    canonicalPaymentClaimDepths_twentyThree_zero]
  decide

/-- Claim depths and claim holes are disjoint by construction. -/
theorem canonicalPaymentClaimDepths_disjoint_claimHoles
    (n : OddNat) (k : ℕ) :
    Disjoint (canonicalPaymentClaimDepths n k)
      (canonicalBlockClaimHoles n k) := by
  classical
  rw [Finset.disjoint_left]
  intro d hdClaim hdHole
  exact (Finset.mem_sdiff.mp hdHole).2 hdClaim

/-- Claims and holes partition the complete positive depth interval. -/
theorem canonicalPaymentClaimDepths_union_claimHoles
    (n : OddNat) (k : ℕ) :
    canonicalPaymentClaimDepths n k ∪ canonicalBlockClaimHoles n k =
      Finset.Icc 1 (canonicalBlockLength n k) := by
  classical
  ext d
  rw [Finset.mem_union, Finset.mem_Icc]
  constructor
  · rintro (hd | hd)
    · rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hd1, hdL, _⟩
      exact ⟨hd1, hdL⟩
    · exact (Finset.mem_sdiff.mp hd).1 |> Finset.mem_Icc.mp
  · intro hd
    by_cases hclaim : d ∈ canonicalPaymentClaimDepths n k
    · exact Or.inl hclaim
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr hd, hclaim⟩)

/-- Claim count plus missing-depth count is exactly block length. -/
theorem canonicalBlockClaimCount_add_claimHoles_card
    (n : OddNat) (k : ℕ) :
    canonicalBlockClaimCount n k + (canonicalBlockClaimHoles n k).card =
      canonicalBlockLength n k := by
  have hcard := Finset.card_union_of_disjoint
    (canonicalPaymentClaimDepths_disjoint_claimHoles n k)
  rw [canonicalPaymentClaimDepths_union_claimHoles,
    ← canonicalBlockClaimCount_eq_claimDepths_card, Nat.card_Icc] at hcard
  have hL := one_le_canonicalBlockLength n k
  omega

/-- The successor of a saturated block always misses its deepest claim.

The missing depth is structural: it is the successor start coordinate, whose
own-width carry is one by the saturated predecessor width obstruction.
-/
theorem CanonicalSaturatedBorderBlock.next_length_mem_claimHoles
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockLength n (k + 1) ∈
      canonicalBlockClaimHoles n (k + 1) := by
  classical
  apply Finset.mem_sdiff.mpr
  constructor
  · exact Finset.mem_Icc.mpr
      ⟨one_le_canonicalBlockLength n (k + 1), le_rfl⟩
  · intro hclaim
    have hcarry := (mem_canonicalPaymentClaimDepths_iff.mp hclaim).2.2
    unfold CarryTwoDebtAt at hcarry
    rw [canonicalPaymentSourceAtDepth_length_eq_startTime] at hcarry
    change stateUpperCarry (canonicalBlockStartState n (k + 1)) = 2 at hcarry
    rw [h.nextStart_stateUpperCarry_eq_one] at hcarry
    omega

/-- A saturated predecessor forces a nonempty claim-hole carrier in its
successor. -/
theorem CanonicalSaturatedBorderBlock.one_le_next_claimHoles_card
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    1 ≤ (canonicalBlockClaimHoles n (k + 1)).card :=
  Finset.one_le_card.mpr ⟨_, h.next_length_mem_claimHoles⟩

/-- A saturated predecessor prevents its successor from claiming every block
depth. -/
theorem CanonicalSaturatedBorderBlock.next_claimCount_le_length_sub_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockClaimCount n (k + 1) ≤
      canonicalBlockLength n (k + 1) - 1 := by
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n (k + 1)
  have hhole := h.one_le_next_claimHoles_card
  omega

/-- Primary signed block-accounting normal form: drift is block length minus
terminal capacity minus the missing claim depths. -/
theorem endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      (canonicalBlockLength n k : ℤ) -
        canonicalBlockTerminalValuation n k -
          (canonicalBlockClaimHoles n k).card := by
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  omega

/-- At terminal valuation one the selected depth is exactly one. -/
theorem canonicalSelectedPositivePressureDepth_eq_one_of_terminalValuation_eq_one
    {n : OddNat} {k : ℕ}
    (hv : canonicalBlockTerminalValuation n k = 1) :
    canonicalSelectedPositivePressureDepth n k = 1 := by
  simp [canonicalSelectedPositivePressureDepth, hv]

/-- At terminal valuation one the selected carrier has cardinality `L - 2`. -/
theorem card_selectedPressureCarrier_of_terminalValuation_eq_one
    {n : OddNat} {k : ℕ}
    (hv : canonicalBlockTerminalValuation n k = 1) :
    (canonicalSelectedPressureCarrier n k).card =
      canonicalBlockLength n k - 2 := by
  unfold canonicalSelectedPressureCarrier
  rw [canonicalPaymentBlockContinuationFiber_card]
  simp only [canonicalSelectedPositivePressureDepth, hv, ↓reduceIte, Nat.reduceAdd]
  change canonicalBlockLength n k - 2 = canonicalBlockLength n k - 2
  rfl

/-- At valuation one, every hole after the first one is exactly one spare
selected incidence. -/
theorem card_selectedDriftSpareCarrier_eq_claimHoles_card_sub_one
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : canonicalBlockTerminalValuation n k = 1) :
    (canonicalSelectedDriftSpareCarrier n k).card =
      (canonicalBlockClaimHoles n k).card - 1 := by
  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
  have hselected := card_selectedPressureCarrier_of_terminalValuation_eq_one hv
  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
  omega

/-- At terminal valuation at least two, claim holes and spare selected
incidences have exactly the same cardinality. -/
theorem card_selectedDriftSpareCarrier_eq_claimHoles_card
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    (canonicalSelectedDriftSpareCarrier n k).card =
      (canonicalBlockClaimHoles n k).card := by
  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
  have hselected : (canonicalSelectedPressureCarrier n k).card =
      canonicalBlockLength n k - canonicalBlockTerminalValuation n k := by
    unfold canonicalSelectedPressureCarrier
    rw [canonicalPaymentBlockContinuationFiber_card,
      canonicalSelectedPositivePressureDepth, if_neg (by omega)]
    change canonicalBlockLength n k -
      (canonicalBlockTerminalValuation n k - 1 + 1) =
        canonicalBlockLength n k - canonicalBlockTerminalValuation n k
    omega
  omega

/-- At terminal valuation at least two, a spare incidence exists exactly when
there is a missing claim depth. -/
theorem selectedDriftSpareCarrier_nonempty_iff_claimHoles_nonempty_of_val_ge_two
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    (canonicalSelectedDriftSpareCarrier n k).Nonempty ↔
      (canonicalBlockClaimHoles n k).Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos,
    card_selectedDriftSpareCarrier_eq_claimHoles_card hpos hnot hv]

/-- Tight positive valuation-one blocks are precisely the candidate class in
which selected drift consumes every selected incidence. -/
def CanonicalTightValuationOnePositiveBlock
    (n : OddNat) (k : ℕ) : Prop :=
  0 < endpointAccountingTerm n k ∧
    ¬ CanonicalSaturatedBorderBlock n k ∧
      canonicalBlockTerminalValuation n k = 1 ∧
        canonicalBlockClaimCount n k = canonicalBlockLength n k - 1

/-- Hole normal form of the tight valuation-one class. -/
theorem canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
    (n : OddNat) (k : ℕ) :
    CanonicalTightValuationOnePositiveBlock n k ↔
      0 < endpointAccountingTerm n k ∧
        ¬ CanonicalSaturatedBorderBlock n k ∧
          canonicalBlockTerminalValuation n k = 1 ∧
            (canonicalBlockClaimHoles n k).card = 1 := by
  unfold CanonicalTightValuationOnePositiveBlock
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  have hL := one_le_canonicalBlockLength n k
  constructor <;> rintro ⟨hpos, hnot, hv, hcount⟩
  · exact ⟨hpos, hnot, hv, by omega⟩
  · exact ⟨hpos, hnot, hv, by omega⟩

/-- A positive nonsaturated valuation-one block has a spare incidence exactly
when it has at least two claim holes. -/
theorem selectedDriftSpareCarrier_nonempty_iff_two_le_claimHoles_card_of_val_one
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : canonicalBlockTerminalValuation n k = 1) :
    (canonicalSelectedDriftSpareCarrier n k).Nonempty ↔
      2 ≤ (canonicalBlockClaimHoles n k).card := by
  rw [← Finset.card_pos,
    card_selectedDriftSpareCarrier_eq_claimHoles_card_sub_one hpos hnot hv]
  omega

/-- Under the positive nonsaturated valuation-one hypotheses, no spare source
incidence is exactly the near-full-claims condition. -/
theorem selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : canonicalBlockTerminalValuation n k = 1) :
    canonicalSelectedDriftSpareCarrier n k = ∅ ↔
      canonicalBlockClaimCount n k = canonicalBlockLength n k - 1 := by
  have hclaimsLe := canonicalBlockClaimCount_le_length n k
  have hvlt :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
  have htoNat : Int.toNat (endpointAccountingTerm n k) =
      canonicalBlockClaimCount n k - 1 := by
    have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
        endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
    exact_mod_cast (show (Int.toNat (endpointAccountingTerm n k) : ℤ) =
      (canonicalBlockClaimCount n k - 1 : ℕ) by omega)
  have himage := card_canonicalSelectedDriftImageCarrier hpos hnot
  have hselected := card_selectedPressureCarrier_of_terminalValuation_eq_one hv
  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n k
  constructor
  · intro hempty
    have hspare : (canonicalSelectedDriftSpareCarrier n k).card = 0 := by
      rw [hempty]
      rfl
    omega
  · intro hclaims
    apply Finset.card_eq_zero.mp
    omega

/-- Tight valuation-one blocks expose all exact no-spare data. -/
theorem CanonicalTightValuationOnePositiveBlock.exact_data
    {n : OddNat} {k : ℕ}
    (h : CanonicalTightValuationOnePositiveBlock n k) :
    canonicalBlockTerminalValuation n k = 1 ∧
      canonicalSelectedPositivePressureDepth n k = 1 ∧
        endpointAccountingTerm n k =
          (canonicalBlockLength n k - 2 : ℕ) ∧
          (canonicalSelectedPressureCarrier n k).card =
            canonicalBlockLength n k - 2 ∧
            canonicalSelectedDriftSpareCarrier n k = ∅ := by
  rcases h with ⟨hpos, hnot, hv, hclaims⟩
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hv, hclaims] at hdrift
  have hvlt :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  exact ⟨hv,
    canonicalSelectedPositivePressureDepth_eq_one_of_terminalValuation_eq_one hv,
    by exact_mod_cast (show endpointAccountingTerm n k =
      (canonicalBlockLength n k - 2 : ℕ) by omega),
    card_selectedPressureCarrier_of_terminalValuation_eq_one hv,
    (selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
      hpos hnot hv).2 hclaims⟩

/-- Zero drift forces exact equality between claims and terminal capacity. -/
theorem claimCount_eq_terminalValuation_of_endpointAccountingTerm_eq_zero
    {n : OddNat} {k : ℕ} (hzero : endpointAccountingTerm n k = 0) :
    canonicalBlockClaimCount n k = canonicalBlockTerminalValuation n k := by
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hzero] at hdrift
  omega

/-- Zero-drift valuation-one blocks have empty selected carrier exactly at
length at most two. -/
theorem selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
    {n : OddNat} {k : ℕ}
    (_hzero : endpointAccountingTerm n k = 0)
    (hv : canonicalBlockTerminalValuation n k = 1) :
    canonicalSelectedPressureCarrier n k = ∅ ↔
      canonicalBlockLength n k ≤ 2 := by
  rw [← Finset.card_eq_zero, card_selectedPressureCarrier_of_terminalValuation_eq_one hv]
  omega

/-- For terminal valuation at least two, the zero-drift selected carrier is
empty exactly when block length does not exceed terminal valuation. -/
theorem selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
    {n : OddNat} {k : ℕ}
    (_hzero : endpointAccountingTerm n k = 0)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    canonicalSelectedPressureCarrier n k = ∅ ↔
      canonicalBlockLength n k ≤ canonicalBlockTerminalValuation n k := by
  rw [← Finset.card_eq_zero]
  unfold canonicalSelectedPressureCarrier
  rw [canonicalPaymentBlockContinuationFiber_card]
  rw [canonicalSelectedPositivePressureDepth, if_neg (by omega)]
  change canonicalBlockLength n k -
      (canonicalBlockTerminalValuation n k - 1 + 1) = 0 ↔
    canonicalBlockLength n k ≤ canonicalBlockTerminalValuation n k
  omega

/-- Rigid balanced border: zero drift and no selected source incidence. -/
def CanonicalZeroCarrierBalancedBorderBlock
    (n : OddNat) (k : ℕ) : Prop :=
  endpointAccountingTerm n k = 0 ∧
    canonicalSelectedPressureCarrier n k = ∅

/-- Exact arithmetic normal form of a zero-drift block with no selected source
incidence. -/
theorem canonicalZeroCarrierBalancedBorderBlock_iff
    (n : OddNat) (k : ℕ) :
    CanonicalZeroCarrierBalancedBorderBlock n k ↔
      (canonicalBlockLength n k = canonicalBlockTerminalValuation n k ∧
        canonicalBlockClaimCount n k = canonicalBlockLength n k) ∨
      (canonicalBlockTerminalValuation n k = 1 ∧
        canonicalBlockLength n k = 2 ∧
        canonicalBlockClaimCount n k = 1) := by
  constructor
  · rintro ⟨hzero, hempty⟩
    have hclaim := claimCount_eq_terminalValuation_of_endpointAccountingTerm_eq_zero hzero
    have hclaimLe := canonicalBlockClaimCount_le_length n k
    have hvpos := one_le_canonicalBlockTerminalValuation n k
    by_cases hv : canonicalBlockTerminalValuation n k = 1
    · have hL :=
        (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
          hzero hv).1 hempty
      by_cases hLen : canonicalBlockLength n k = 1
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨hv, by omega, by omega⟩
    · have hv2 : 2 ≤ canonicalBlockTerminalValuation n k := by omega
      have hL :=
        (selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
          hzero hv2).1 hempty
      exact Or.inl ⟨by omega, by omega⟩
  · rintro (hfull | hexceptional)
    · rcases hfull with ⟨hLv, hclaimL⟩
      have hzero := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
      rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaimL, hLv] at hzero
      have hvpos := one_le_canonicalBlockTerminalValuation n k
      by_cases hv : canonicalBlockTerminalValuation n k = 1
      · refine ⟨by omega,
          (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
            (by omega) hv).2 (by omega)⟩
      · refine ⟨by omega,
          (selectedPressureCarrier_eq_empty_iff_length_le_terminalValuation_of_zero
            (by omega) (by omega)).2 (by omega)⟩
    · rcases hexceptional with ⟨hv, hL, hclaim⟩
      have hzero := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
      rw [canonicalBlockCapacityCount_eq_terminalValuation, hv, hclaim] at hzero
      exact ⟨by omega,
        (selectedPressureCarrier_eq_empty_iff_length_le_two_of_zero_val_one
          (by omega) hv).2 (by omega)⟩

/-- The full balanced no-carrier branch has no claim holes. -/
theorem claimHoles_card_eq_zero_of_full_balanced
    {n : OddNat} {k : ℕ}
    (hL : canonicalBlockLength n k = canonicalBlockTerminalValuation n k)
    (hclaim : canonicalBlockClaimCount n k = canonicalBlockLength n k) :
    (canonicalBlockClaimHoles n k).card = 0 := by
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  omega

/-- The exceptional length-two balanced branch has one missing claim depth. -/
theorem claimHoles_card_eq_one_of_exceptional_length_two_balanced
    {n : OddNat} {k : ℕ}
    (hL : canonicalBlockLength n k = 2)
    (hclaim : canonicalBlockClaimCount n k = 1) :
    (canonicalBlockClaimHoles n k).card = 1 := by
  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n k
  omega

/-! ### Unique missing claim depth -/

/-- The unique missing depth of a block whose claim-hole carrier has
cardinality one. -/
noncomputable def canonicalBlockMissingClaimDepth
    {n : OddNat} {k : ℕ}
    (h : (canonicalBlockClaimHoles n k).card = 1) : ℕ :=
  (Finset.card_eq_one.mp h).choose

/-- The one-hole carrier is the singleton containing its chosen missing
depth. -/
theorem canonicalBlockClaimHoles_eq_singleton_missingDepth
    {n : OddNat} {k : ℕ}
    (h : (canonicalBlockClaimHoles n k).card = 1) :
    canonicalBlockClaimHoles n k = {canonicalBlockMissingClaimDepth h} := by
  exact (Finset.card_eq_one.mp h).choose_spec

/-- With one missing depth, the claim-depth carrier is exactly the complete
positive interval with that depth erased. -/
theorem canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
    {n : OddNat} {k : ℕ}
    (h : (canonicalBlockClaimHoles n k).card = 1) :
    canonicalPaymentClaimDepths n k =
      (Finset.Icc 1 (canonicalBlockLength n k)).erase
        (canonicalBlockMissingClaimDepth h) := by
  classical
  let missing := canonicalBlockMissingClaimDepth h
  have hholes : canonicalBlockClaimHoles n k = {missing} :=
    canonicalBlockClaimHoles_eq_singleton_missingDepth h
  ext d
  rw [Finset.mem_erase, Finset.mem_Icc]
  constructor
  · intro hdClaim
    rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
      ⟨hd1, hdL, _⟩
    refine ⟨?_, hd1, hdL⟩
    intro hdm
    have hmHole : missing ∈ canonicalBlockClaimHoles n k := by
      rw [hholes]
      simp
    exact (Finset.mem_sdiff.mp hmHole).2 (by simpa [hdm] using hdClaim)
  · rintro ⟨hdm, hd1, hdL⟩
    by_contra hdClaim
    have hdHole : d ∈ canonicalBlockClaimHoles n k :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdL⟩, hdClaim⟩
    have : d = missing := by
      rw [hholes] at hdHole
      simpa using hdHole
    exact hdm this

/-- The unique missing depth is either the endpoint depth or a delayed depth. -/
theorem canonicalBlockMissingClaimDepth_eq_one_or_gt_one
    {n : OddNat} {k : ℕ}
    (h : (canonicalBlockClaimHoles n k).card = 1) :
    canonicalBlockMissingClaimDepth h = 1 ∨
      1 < canonicalBlockMissingClaimDepth h := by
  have hmem : canonicalBlockMissingClaimDepth h ∈ canonicalBlockClaimHoles n k := by
    rw [canonicalBlockClaimHoles_eq_singleton_missingDepth h]
    simp
  have hIcc := (Finset.mem_sdiff.mp hmem).1
  have hone := (Finset.mem_Icc.mp hIcc).1
  omega

/-- Tight valuation-one positive blocks have a unique missing claim depth. -/
theorem CanonicalTightValuationOnePositiveBlock.claimDepths_eq_erase_missing
    {n : OddNat} {k : ℕ} (h : CanonicalTightValuationOnePositiveBlock n k) :
    canonicalPaymentClaimDepths n k =
      (Finset.Icc 1 (canonicalBlockLength n k)).erase
        (canonicalBlockMissingClaimDepth
          ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
            n k).1 h).2.2.2) :=
  canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
    ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one n k).1 h).2.2.2

/-- The exceptional length-two balanced branch also has a unique missing claim
depth. -/
theorem exceptionalLengthTwoBalanced_claimDepths_eq_erase_missing
    {n : OddNat} {k : ℕ}
    (hL : canonicalBlockLength n k = 2)
    (hclaim : canonicalBlockClaimCount n k = 1) :
    canonicalPaymentClaimDepths n k =
      (Finset.Icc 1 (canonicalBlockLength n k)).erase
        (canonicalBlockMissingClaimDepth
          (claimHoles_card_eq_one_of_exceptional_length_two_balanced hL hclaim)) :=
  canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
    (claimHoles_card_eq_one_of_exceptional_length_two_balanced hL hclaim)

/-- A zero-carrier balanced successor of a saturated block is forced into the
exceptional length-two branch; the full-balanced branch is excluded by the
successor's mandatory deepest hole. -/
theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_exact_data
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
    canonicalBlockLength n (k + 1) = 2 ∧
      canonicalBlockTerminalValuation n (k + 1) = 1 ∧
        canonicalBlockClaimCount n (k + 1) = 1 := by
  rcases (canonicalZeroCarrierBalancedBorderBlock_iff n (k + 1)).1 hzero with
    hfull | hexceptional
  · have hholes := claimHoles_card_eq_zero_of_full_balanced hfull.1 hfull.2
    have hnonempty := h.one_le_next_claimHoles_card
    omega
  · exact ⟨hexceptional.2.1, hexceptional.1, hexceptional.2.2⟩

/-- The exceptional successor holes consist exactly of its deepest depth. -/
theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_claimHoles_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
    canonicalBlockClaimHoles n (k + 1) = {2} := by
  have hdata := h.zeroCarrierBalanced_next_exact_data hzero
  have hcard := claimHoles_card_eq_one_of_exceptional_length_two_balanced
    hdata.1 hdata.2.2
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hmem := h.next_length_mem_claimHoles
  rw [hdata.1, ha] at hmem
  simp only [Finset.mem_singleton] at hmem
  simpa [hmem] using ha

/-- The exceptional successor claim carrier is the singleton endpoint depth. -/
theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_claimDepths_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
    canonicalPaymentClaimDepths n (k + 1) = {1} := by
  classical
  have hdata := h.zeroCarrierBalanced_next_exact_data hzero
  have hholes := h.zeroCarrierBalanced_next_claimHoles_eq hzero
  ext d
  constructor
  · intro hd
    have hi := (mem_canonicalPaymentClaimDepths_iff.mp hd)
    have hiL : d ≤ canonicalBlockLength n (k + 1) := by
      simpa [canonicalBlockLength] using hi.2.1
    have hne : d ≠ 2 := by
      intro heq
      have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) := by
        rw [hholes, heq]
        simp
      exact (Finset.mem_sdiff.mp hhole).2 hd
    simp only [Finset.mem_singleton]
    omega
  · intro hd
    simp only [Finset.mem_singleton] at hd
    subst d
    by_contra hnot
    have hhole : 1 ∈ canonicalBlockClaimHoles n (k + 1) :=
      Finset.mem_sdiff.mpr ⟨by simp [hdata.1], hnot⟩
    rw [hholes] at hhole
    simp at hhole

/-- A tight valuation-one positive successor misses exactly its deepest depth. -/
theorem CanonicalSaturatedBorderBlock.tightValOne_next_claimHoles_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (htight : CanonicalTightValuationOnePositiveBlock n (k + 1)) :
    canonicalBlockClaimHoles n (k + 1) =
      {canonicalBlockLength n (k + 1)} := by
  have hcard :=
    ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
      n (k + 1)).1 htight).2.2.2
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hmem := h.next_length_mem_claimHoles
  rw [ha] at hmem
  simp only [Finset.mem_singleton] at hmem
  simpa [hmem] using ha

/-- A tight valuation-one positive successor claims every depth strictly below
its deepest depth. -/
theorem CanonicalSaturatedBorderBlock.tightValOne_next_claimDepths_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (htight : CanonicalTightValuationOnePositiveBlock n (k + 1)) :
    canonicalPaymentClaimDepths n (k + 1) =
      Finset.Icc 1 (canonicalBlockLength n (k + 1) - 1) := by
  classical
  have hholes := h.tightValOne_next_claimHoles_eq htight
  ext d
  constructor
  · intro hd
    have hi := mem_canonicalPaymentClaimDepths_iff.mp hd
    have hiL : d ≤ canonicalBlockLength n (k + 1) := by
      simpa [canonicalBlockLength] using hi.2.1
    have hne : d ≠ canonicalBlockLength n (k + 1) := by
      intro heq
      have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) := by
        rw [hholes, heq]
        simp
      exact (Finset.mem_sdiff.mp hhole).2 hd
    simp only [Finset.mem_Icc]
    omega
  · intro hd
    simp only [Finset.mem_Icc] at hd
    by_contra hnot
    have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hd.1, by omega⟩, hnot⟩
    rw [hholes] at hhole
    simp only [Finset.mem_singleton] at hhole
    omega

/-! ## Saturated-successor source classification

The five-way classification proposed at cp-325 omitted a logically possible
positive valuation-one branch: the spare carrier need not be empty.  The
six-way theorem below is therefore the exhaustive surface justified by the
current API.  Collapsing it to five branches requires a new theorem saying
that every positive nonsaturated valuation-one successor of a saturated block
is tight; no such theorem is currently available.
-/

/-- A zero-drift block with a nonempty selected carrier supplies an actual
source incidence, independently of the (empty) drift image. -/
theorem exists_selectedPressureSource_of_zero_of_nonempty
    {n : OddNat} {k : ℕ}
    (_hzero : endpointAccountingTerm n k = 0)
    (hcarrier : (canonicalSelectedPressureCarrier n k).Nonempty) :
    ∃ i, i ∈ canonicalSelectedPressureCarrier n k :=
  hcarrier

/-- A positive nonsaturated block of terminal valuation at least two supplies
an actual spare selected source incidence. -/
theorem exists_spareSelectedPressureSource_of_pos_of_two_le_terminalValuation
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    ∃ i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k},
      i ∈ canonicalSelectedDriftSpareCarrier n k :=
  canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv

/-- A successor has an immediately chargeable spare selected incidence. -/
def CanonicalSuccessorSpareAvailable (n : OddNat) (j : ℕ) : Prop :=
  (canonicalSelectedDriftSpareCarrier n j).Nonempty

/-- With zero drift the chosen drift image is empty, so every selected source
incidence is spare. -/
theorem successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty
    {n : OddNat} {j : ℕ}
    (hzero : endpointAccountingTerm n j = 0)
    (hcarrier : (canonicalSelectedPressureCarrier n j).Nonempty) :
    CanonicalSuccessorSpareAvailable n j := by
  have himage : canonicalSelectedDriftImageCarrier n j = ∅ :=
    canonicalSelectedDriftImageCarrier_eq_empty_of_not_active (by
      intro hactive
      omega)
  have hsplit := card_selectedPressureCarrier_eq_driftImage_add_spare n j
  rw [himage] at hsplit
  simp only [Finset.card_empty, zero_add] at hsplit
  apply Finset.card_pos.mp
  have hcard : 0 < (canonicalSelectedPressureCarrier n j).card :=
    Finset.card_pos.mpr hcarrier
  omega

/-- Exhaustive successor classification currently justified for a saturated
predecessor.  The final disjunct is the valuation-one spare branch missing
from the proposed five-way split. -/
theorem CanonicalSaturatedBorderBlock.successor_source_classification
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n (k + 1) < 0 ∨
      (endpointAccountingTerm n (k + 1) = 0 ∧
        (canonicalSelectedPressureCarrier n (k + 1)).Nonempty) ∨
      CanonicalZeroCarrierBalancedBorderBlock n (k + 1) ∨
      (0 < endpointAccountingTerm n (k + 1) ∧
        ¬ CanonicalSaturatedBorderBlock n (k + 1) ∧
        2 ≤ canonicalBlockTerminalValuation n (k + 1)) ∨
      CanonicalTightValuationOnePositiveBlock n (k + 1) ∨
      (0 < endpointAccountingTerm n (k + 1) ∧
        ¬ CanonicalSaturatedBorderBlock n (k + 1) ∧
        canonicalBlockTerminalValuation n (k + 1) = 1 ∧
        (canonicalSelectedDriftSpareCarrier n (k + 1)).Nonempty) := by
  classical
  let j := k + 1
  have hnotsat : ¬ CanonicalSaturatedBorderBlock n j := by
    simpa [j] using h.not_succ
  by_cases hneg : endpointAccountingTerm n j < 0
  · exact Or.inl hneg
  · have hnonneg : 0 ≤ endpointAccountingTerm n j := by omega
    by_cases hzero : endpointAccountingTerm n j = 0
    · by_cases hempty : canonicalSelectedPressureCarrier n j = ∅
      · exact Or.inr (Or.inr (Or.inl ⟨hzero, hempty⟩))
      · exact Or.inr (Or.inl ⟨hzero, Finset.nonempty_iff_ne_empty.mpr hempty⟩)
    · have hpos : 0 < endpointAccountingTerm n j := by omega
      by_cases hv : canonicalBlockTerminalValuation n j = 1
      · by_cases hspare : canonicalSelectedDriftSpareCarrier n j = ∅
        · have hclaims :=
            (selectedDriftSpareCarrier_eq_empty_iff_claimCount_eq_length_sub_one
              hpos hnotsat hv).1 hspare
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hpos, hnotsat, hv, hclaims⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hpos, hnotsat, hv, Finset.nonempty_iff_ne_empty.mpr hspare⟩))))
      · have hvpos := one_le_canonicalBlockTerminalValuation n j
        have hv2 : 2 ≤ canonicalBlockTerminalValuation n j := by omega
        have hbranch : 0 < endpointAccountingTerm n j ∧
            ¬ CanonicalSaturatedBorderBlock n j ∧
            2 ≤ canonicalBlockTerminalValuation n j := ⟨hpos, hnotsat, hv2⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [j] using hbranch))))

/-- Source-level compression of the detailed six-way successor theorem. -/
theorem CanonicalSaturatedBorderBlock.successor_negative_or_spare_or_rigid
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n (k + 1) < 0 ∨
      CanonicalSuccessorSpareAvailable n (k + 1) ∨
      CanonicalZeroCarrierBalancedBorderBlock n (k + 1) ∨
      CanonicalTightValuationOnePositiveBlock n (k + 1) := by
  rcases h.successor_source_classification with
    hneg | hzeroSpare | hzeroRigid | hpos2 | htight | hpos1Spare
  · exact Or.inl hneg
  · exact Or.inr (Or.inl
      (successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty
        hzeroSpare.1 hzeroSpare.2))
  · exact Or.inr (Or.inr (Or.inl hzeroRigid))
  · exact Or.inr (Or.inl
      (canonicalSelectedDriftSpareCarrier_nonempty hpos2.1 hpos2.2.1 hpos2.2.2))
  · exact Or.inr (Or.inr (Or.inr htight))
  · exact Or.inr (Or.inl hpos1Spare.2.2.2)

/-- A negative successor cancels the saturated predecessor's exact unit
drift numerically. -/
theorem CanonicalSaturatedBorderBlock.drift_add_successor_drift_nonpos_of_negative
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hneg : endpointAccountingTerm n (k + 1) < 0) :
    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0 := by
  rw [h.netDrift_eq_one]
  omega

/-- Every spare-available successor supplies an explicit singleton embedding
into its actual spare source carrier. -/
noncomputable def oneEmbedding_successorSpareCarrier
    {n : OddNat} {j : ℕ} (h : CanonicalSuccessorSpareAvailable n j) :
    Fin 1 ↪ {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j} //
      i ∈ canonicalSelectedDriftSpareCarrier n j} := by
  classical
  let : Fintype
      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j} //
        i ∈ canonicalSelectedDriftSpareCarrier n j} :=
    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n j) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_fin, Fintype.card_coe]
  exact Finset.one_le_card.mpr h

/-! ## Experimental dyadic depth-transfer potential

These inequalities compare numerical denominations only.  They do not define
a cross-depth map, do not permit one source incidence to be reused at several
depths, and do not establish causal repayment.  A later conversion layer must
carry an explicit nonduplication invariant before these bounds can be used as
matching capacity.
-/

/-- Positive nonsaturated drift fits in the selected continuation width after
removing its selected depth and the endpoint. -/
theorem intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    Int.toNat (endpointAccountingTerm n k) ≤
      canonicalBlockLength n k -
        canonicalSelectedPositivePressureDepth n k - 1 := by
  let d := canonicalSelectedPositivePressureDepth n k
  let L := canonicalBlockLength n k
  have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
    hpos hnot
  have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hnot
  have hcard : (canonicalSelectedPressureCarrier n k).card = L - (d + 1) := by
    unfold canonicalSelectedPressureCarrier
    rw [canonicalPaymentBlockContinuationFiber_card]
    rfl
  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
  rw [hcard] at hle
  change d < L at hdL
  change Int.toNat (endpointAccountingTerm n k) ≤ L - d - 1
  exact_mod_cast (show ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) ≤
    (L - d - 1 : ℕ) by omega)

/-- Positive nonsaturated blocks have room for a positive selected depth, a
positive gap, and an endpoint, hence length at least three. -/
theorem three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    3 ≤ canonicalBlockLength n k := by
  have hbound :=
    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
  have hcast : ((Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) =
      endpointAccountingTerm n k := Int.toNat_of_nonneg hpos.le
  have ha : 0 < Int.toNat (endpointAccountingTerm n k) := by omega
  have hd := one_le_canonicalSelectedPositivePressureDepth n k
  omega

/-- Elementary half-budget inequality used by the dyadic denomination. -/
theorem nat_le_two_pow_pred {gap : ℕ} (hgap : 1 ≤ gap) :
    gap ≤ 2 ^ (gap - 1) := by
  rcases gap with _ | gap
  · omega
  · rcases gap with _ | gap
    · norm_num
    · have hpow := (gap + 1).lt_two_pow_self
      have hle := Nat.succ_le_of_lt hpow
      simpa only [Nat.add_sub_cancel, Nat.succ_eq_add_one] using hle

/-- Strengthened local dyadic potential: positive nonsaturated demand fits in
one half of the block-width budget. -/
theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    Int.toNat (endpointAccountingTerm n k) *
        2 ^ canonicalSelectedPositivePressureDepth n k ≤
      2 ^ (canonicalBlockLength n k - 2) := by
  let a := Int.toNat (endpointAccountingTerm n k)
  let d := canonicalSelectedPositivePressureDepth n k
  let L := canonicalBlockLength n k
  let gap := L - d - 1
  have ha : a ≤ gap :=
    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
  have hcast : ((a : ℕ) : ℤ) = endpointAccountingTerm n k :=
    Int.toNat_of_nonneg hpos.le
  have hapos : 0 < a := by omega
  have hgap : 1 ≤ gap := by omega
  have hgapPow : gap ≤ 2 ^ (gap - 1) := nat_le_two_pow_pred hgap
  have hsum : (gap - 1) + d = L - 2 := by
    have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
      hpos hnot
    change d < L at hdL
    dsimp [gap]
    omega
  calc
    a * 2 ^ d ≤ gap * 2 ^ d := Nat.mul_le_mul_right _ ha
    _ ≤ 2 ^ (gap - 1) * 2 ^ d := Nat.mul_le_mul_right _ hgapPow
    _ = 2 ^ ((gap - 1) + d) := by rw [pow_add]
    _ = 2 ^ (L - 2) := by rw [hsum]

/-- A saturated unit and the positive demand of its nonsaturated successor fit
in the successor's full local dyadic budget. -/
theorem CanonicalSaturatedBorderBlock.two_add_successor_dyadic_demand_le
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hpos : 0 < endpointAccountingTerm n (k + 1)) :
    2 + Int.toNat (endpointAccountingTerm n (k + 1)) *
        2 ^ canonicalSelectedPositivePressureDepth n (k + 1) ≤
      2 ^ (canonicalBlockLength n (k + 1) - 1) := by
  have hnot := h.not_succ
  have hdemand :=
    intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
      hpos hnot
  have hL :=
    three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
      hpos hnot
  have htwo : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 2) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤
      canonicalBlockLength n (k + 1) - 2 by omega)
    simpa using this
  rw [show canonicalBlockLength n (k + 1) - 1 =
      (canonicalBlockLength n (k + 1) - 2) + 1 by omega, pow_succ]
  omega

/-- A zero-drift successor of length at least two has enough numerical dyadic
budget for the preceding saturated unit. -/
theorem two_le_successor_dyadic_budget_of_two_le_length
    {n : OddNat} {k : ℕ}
    (_hzero : endpointAccountingTerm n (k + 1) = 0)
    (hL : 2 ≤ canonicalBlockLength n (k + 1)) :
    2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
    (show 1 ≤ canonicalBlockLength n (k + 1) - 1 by omega)
  simpa using this

/-- Abstract block-width dyadic budget. -/
abbrev CanonicalAbstractDyadicBudgetCarrier
    (n : OddNat) (k : ℕ) :=
  Fin (2 ^ (canonicalBlockLength n k - 1))

/-- Abstract selected positive-drift demand at its dyadic depth. -/
abbrev CanonicalAbstractDyadicDemandCarrier
    (n : OddNat) (k : ℕ) :=
  Fin (Int.toNat (endpointAccountingTerm n k) *
    2 ^ canonicalSelectedPositivePressureDepth n k)

/-- A zero-drift successor of length at least two carries the preceding
saturated mass-two unit in the low two slots of its abstract budget. -/
noncomputable def abstractZeroSuccessorUnitEmbedding
    {n : OddNat} {k : ℕ}
    (_hzero : endpointAccountingTerm n (k + 1) = 0)
    (hL : 2 ≤ canonicalBlockLength n (k + 1)) :
    Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1) where
  toFun i := by
    refine ⟨i.val, ?_⟩
    have htwo : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) :=
      two_le_successor_dyadic_budget_of_two_le_length _hzero hL
    omega
  inj' := by
    intro i j hij
    have hval := congrArg Fin.val hij
    change i.val = j.val at hval
    exact Fin.ext hval

/-- Local dyadic potential: the selected positive drift, denominated at depth
`d`, is bounded by one block-width denomination `2^(L-1)`. -/
theorem intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_one
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    Int.toNat (endpointAccountingTerm n k) *
        2 ^ canonicalSelectedPositivePressureDepth n k ≤
      2 ^ (canonicalBlockLength n k - 1) := by
  let a := Int.toNat (endpointAccountingTerm n k)
  let d := canonicalSelectedPositivePressureDepth n k
  let L := canonicalBlockLength n k
  let gap := L - d - 1
  have hdL := selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
    hpos hnot
  have ha : a ≤ gap :=
    intToNat_endpointAccountingTerm_le_length_sub_depth_sub_one hpos hnot
  have hagap : a ≤ 2 ^ gap :=
    ha.trans (Nat.le_of_lt gap.lt_two_pow_self)
  have hsum : gap + d = L - 1 := by
    change d < L at hdL
    dsimp [gap]
    omega
  calc
    a * 2 ^ d ≤ 2 ^ gap * 2 ^ d := Nat.mul_le_mul_right _ hagap
    _ = 2 ^ (gap + d) := by rw [pow_add]
    _ = 2 ^ (L - 1) := by rw [hsum]

/-- The explicit saturated unit has exactly the same dyadic mass as its fixed
length-two block-width denomination. -/
theorem CanonicalSaturatedBorderBlock.dyadic_unit_budget
    {n : OddNat} {k : ℕ} (_h : CanonicalSaturatedBorderBlock n k) :
    (1 : ℕ) * 2 ^ 1 = 2 ^ (2 - 1) := by
  norm_num

/-! ## Length-one successor residue audit

The saturated predecessor has odd core congruent to either three or seven
modulo eight.  A successor of length one excludes the seven class, because the
existing successor normal form forces length at least two there.  This is the
finite residue grammar needed before attempting a modulo-sixteen refinement.

The stronger candidate

`successor length = 1` and `successor terminal valuation = 1`
`-> predecessor odd core % 16 = 11`

is proved below by first exposing the successor odd-core and terminal-carrier
substitutions.  The resulting modulo-thirty-two continuation grammar also
records the next genuine boundary: predecessor residue alone does not
transport the following block's claim count.
-/

/-- A length-one successor of a saturated block selects the class three
modulo eight for the predecessor odd core. -/
theorem CanonicalSaturatedBorderBlock.oddCore_mod_eight_eq_three_of_next_length_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockOddCore n k % 8 = 3 := by
  rcases h.oddCore_mod_eight_eq_three_or_seven with hthree | hseven
  · exact hthree
  · have htwo := h.two_le_nextBlockLength_of_core_mod_eight_eq_seven hseven
    omega

/-- Exact odd-core substitution for a length-one successor. -/
theorem CanonicalSaturatedBorderBlock.nextOddCore_eq_quarter_nine_core_add_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockOddCore n (k + 1) =
      (9 * canonicalBlockOddCore n k + 1) / 4 := by
  let u := canonicalBlockOddCore n k
  let u' := canonicalBlockOddCore n (k + 1)
  have hstart := canonicalBlockStartState_add_one_eq_pow_mul_oddCore n (k + 1)
  have hnext := h.nextStartState_add_one_eq
  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n k
  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
  have hu : u = 8 * (u / 8) + 3 := by
    have := Nat.mod_add_div u 8
    omega
  rw [hL] at hstart
  norm_num at hstart
  have hhalf : (9 * u + 1) / 2 = 36 * (u / 8) + 14 := by
    omega
  have hquarter : (9 * u + 1) / 4 = 18 * (u / 8) + 7 := by
    omega
  dsimp [u] at hu hhalf hquarter
  rw [hhalf] at hnext
  rw [hquarter]
  omega

/-- The terminal carrier of a length-one successor is the exact substituted
quarter-word `(27*u-1)/4`. -/
theorem CanonicalSaturatedBorderBlock.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockTerminalCarrier n (k + 1) =
      (27 * canonicalBlockOddCore n k - 1) / 4 := by
  let u := canonicalBlockOddCore n k
  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
  have hu : u = 8 * (u / 8) + 3 := by
    have := Nat.mod_add_div u 8
    omega
  rw [canonicalBlockTerminalCarrier, hL]
  norm_num
  rw [h.nextOddCore_eq_quarter_nine_core_add_one hL]
  dsimp [u] at hu ⊢
  omega

/-- For the length-one successor, terminal valuation one is exactly the
predecessor residue class eleven modulo sixteen. -/
theorem CanonicalSaturatedBorderBlock.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockTerminalValuation n (k + 1) = 1 ↔
      canonicalBlockOddCore n k % 16 = 11 := by
  let u := canonicalBlockOddCore n k
  let c := canonicalBlockTerminalCarrier n (k + 1)
  have hcpos := canonicalBlockTerminalCarrier_pos n (k + 1)
  have hc := h.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
  have hu8 := h.oddCore_mod_eight_eq_three_of_next_length_one hL
  constructor
  · intro hv
    have hnot4 : ¬ 4 ∣ c := by
      intro hfour
      have htwo := (two_le_v2_iff_four_dvd hcpos.ne').2 hfour
      unfold canonicalBlockTerminalValuation at hv
      omega
    have hrem : u % 16 = 3 ∨ u % 16 = 11 := by
      omega
    rcases hrem with h3 | h11
    · have hu : u = 16 * (u / 16) + 3 := by
        have := Nat.mod_add_div u 16
        omega
      have hcFour : 4 ∣ c := by
        refine ⟨27 * (u / 16) + 5, ?_⟩
        dsimp [c, u] at hc hu ⊢
        omega
      exact (hnot4 hcFour).elim
    · exact h11
  · intro hu16
    have hu : u = 16 * (u / 16) + 11 := by
      have := Nat.mod_add_div u 16
      omega
    have hcform : c = 108 * (u / 16) + 74 := by
      dsimp [c, u] at hc hu ⊢
      omega
    have hceven : c % 2 = 0 := by rw [hcform]; omega
    have hchalfodd : (c / 2) % 2 = 1 := by rw [hcform]; omega
    unfold canonicalBlockTerminalValuation
    change v2 c = 1
    rw [v2_step_of_even c hceven hcpos, v2_odd _ hchalfodd]

/-- For a length-one block, the sole claim-count condition is exactly the
carry-two condition at its endpoint source. -/
theorem canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one
    {n : OddNat} {k : ℕ} (hL : canonicalBlockLength n k = 1) :
    canonicalBlockClaimCount n k = 1 ↔
      CarryTwoDebtAt n (paymentEndpointSeq n k) := by
  constructor
  · intro hcount
    have hcard : (canonicalPaymentClaimDepths n k).card = 1 := by
      simpa [canonicalBlockClaimCount_eq_claimDepths_card] using hcount
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega :
      0 < (canonicalPaymentClaimDepths n k).card)
    have hdepth := mem_canonicalPaymentClaimDepths_iff.mp hd
    have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
    have hdOne : d = 1 := by
      rw [hLen, hL] at hdepth
      omega
    subst d
    exact (one_mem_canonicalPaymentClaimDepths_iff n k).mp hd
  · intro hcarry
    have hone : 1 ∈ canonicalPaymentClaimDepths n k :=
      (one_mem_canonicalPaymentClaimDepths_iff n k).mpr hcarry
    have hpos : 0 < canonicalBlockClaimCount n k := by
      rw [canonicalBlockClaimCount_eq_claimDepths_card]
      exact Finset.card_pos.mpr ⟨1, hone⟩
    have hle := canonicalBlockClaimCount_le_length n k
    omega

/--
Compatibility-only name for the former balanced-carry exception.

This predicate is impossible by
`not_canonicalLengthOneBalancedCarrySuccessor`; new theorems must use
`CanonicalLengthOneTerminalOneSuccessor` instead.
-/
def CanonicalLengthOneBalancedCarrySuccessor
    (n : OddNat) (k : ℕ) : Prop :=
  CanonicalSaturatedBorderBlock n k ∧
    canonicalBlockLength n (k + 1) = 1 ∧
      canonicalBlockTerminalValuation n (k + 1) = 1 ∧
        canonicalBlockClaimCount n (k + 1) = 1

/-- A length-one successor of a saturated block has no marked claim depths. -/
theorem CanonicalSaturatedBorderBlock.next_claimCount_eq_zero_of_length_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockClaimCount n (k + 1) = 0 := by
  have hle := h.next_claimCount_le_length_sub_one
  omega

/-- The former length-one balanced-carry exception is empty. -/
theorem not_canonicalLengthOneBalancedCarrySuccessor
    (n : OddNat) (k : ℕ) :
    ¬ CanonicalLengthOneBalancedCarrySuccessor n k := by
  rintro ⟨hsat, hL, _, hclaim⟩
  have hzero := hsat.next_claimCount_eq_zero_of_length_one hL
  omega

/--
Nonvacuous length-one successor grammar: terminal valuation one, without the
impossible carry-two claim.  This is the correct home for the residue and
following-start arithmetic formerly stated under the empty balanced-carry
predicate.
-/
def CanonicalLengthOneTerminalOneSuccessor
    (n : OddNat) (k : ℕ) : Prop :=
  CanonicalSaturatedBorderBlock n k ∧
    canonicalBlockLength n (k + 1) = 1 ∧
      canonicalBlockTerminalValuation n (k + 1) = 1

/-- Terminal valuation one in a length-one successor is exactly predecessor
odd-core residue eleven modulo sixteen. -/
theorem canonicalLengthOneTerminalOneSuccessor_iff_residue
    (n : OddNat) (k : ℕ) :
    CanonicalLengthOneTerminalOneSuccessor n k ↔
      CanonicalSaturatedBorderBlock n k ∧
        canonicalBlockLength n (k + 1) = 1 ∧
          canonicalBlockOddCore n k % 16 = 11 := by
  constructor
  · rintro ⟨hsat, hL, hv⟩
    exact ⟨hsat, hL,
      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv⟩
  · rintro ⟨hsat, hL, hres⟩
    exact ⟨hsat, hL,
      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres⟩

namespace CanonicalLengthOneTerminalOneSuccessor

/-- The successor carries no claim. -/
theorem claimCount_eq_zero
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
    canonicalBlockClaimCount n (k + 1) = 0 :=
  h.1.next_claimCount_eq_zero_of_length_one h.2.1

/-- The length-one terminal-one successor has drift exactly minus one. -/
theorem successorDrift_eq_neg_one
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
    endpointAccountingTerm n (k + 1) = -1 := by
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
    canonicalBlockCapacityCount_eq_terminalValuation, h.claimCount_eq_zero,
    h.2.2]
  norm_num

/-- The predecessor unit and successor drift cancel as integers. -/
theorem predecessorDrift_add_successorDrift_eq_zero
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) = 0 := by
  rw [h.1.2.2, h.successorDrift_eq_neg_one]
  norm_num

/-- The following block starts at the exact eighth-word `(27*u-1)/8`.
Unlike the historical balanced-carry version, this theorem has a nonempty
hypothesis surface. -/
theorem followingStartState_eq
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
    canonicalBlockStartState n (k + 2) =
      (27 * canonicalBlockOddCore n k - 1) / 8 := by
  rcases h with ⟨hsat, hL, hv⟩
  have hnext := canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
    n (k + 1)
  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n (k + 1)
  have hc := hsat.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
  let u := canonicalBlockOddCore n k
  have hu16 :=
    (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
  have hu : u = 16 * (u / 16) + 11 := by
    have := Nat.mod_add_div u 16
    omega
  rw [show k + 2 = k + 1 + 1 by omega, hsucc, hnext, hv]
  norm_num
  dsimp [u] at hu hu16 ⊢
  rw [hc]
  omega

/-- The nonvacuous modulo-sixteen class has the two expected refinements
modulo thirty-two. -/
theorem core_mod_thirtyTwo_eq_eleven_or_twentySeven
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
    canonicalBlockOddCore n k % 32 = 11 ∨
      canonicalBlockOddCore n k % 32 = 27 := by
  have hres := (canonicalLengthOneTerminalOneSuccessor_iff_residue n k).1 h |>.2.2
  omega

end CanonicalLengthOneTerminalOneSuccessor

/-- In the other length-one residue class, the successor has at least two
units of negative drift. -/
theorem CanonicalSaturatedBorderBlock.nextDrift_le_neg_two_of_length_one_mod16_three
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1)
    (hres : canonicalBlockOddCore n k % 16 = 3) :
    endpointAccountingTerm n (k + 1) ≤ -2 := by
  have hclaim := h.next_claimCount_eq_zero_of_length_one hL
  have hvpos := one_le_canonicalBlockTerminalValuation n (k + 1)
  have hvne : canonicalBlockTerminalValuation n (k + 1) ≠ 1 := by
    intro hv
    have h11 :=
      (h.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
    omega
  have hv : 2 ≤ canonicalBlockTerminalValuation n (k + 1) := by omega
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
    canonicalBlockCapacityCount_eq_terminalValuation, hclaim]
  omega

/-- Residue/carry presentation of the length-one balanced successor. -/
theorem canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
    (n : OddNat) (k : ℕ) :
    CanonicalLengthOneBalancedCarrySuccessor n k ↔
      CanonicalSaturatedBorderBlock n k ∧
        canonicalBlockLength n (k + 1) = 1 ∧
          canonicalBlockOddCore n k % 16 = 11 ∧
            CarryTwoDebtAt n (paymentEndpointSeq n (k + 1)) := by
  constructor
  · rintro ⟨hsat, hL, hv, hclaim⟩
    exact ⟨hsat, hL,
      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv,
      (canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one hL).1
        hclaim⟩
  · rintro ⟨hsat, hL, hres, hcarry⟩
    exact ⟨hsat, hL,
      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres,
      (canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one hL).2
        hcarry⟩

namespace CanonicalLengthOneBalancedCarrySuccessor

/-- The start after the exceptional length-one successor is the exact
eighth-word `(27*u-1)/8`. -/
theorem followingStartState_eq
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k) :
    canonicalBlockStartState n (k + 2) =
      (27 * canonicalBlockOddCore n k - 1) / 8 := by
  rcases h with ⟨hsat, hL, hv, _⟩
  have hnext := canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
    n (k + 1)
  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n (k + 1)
  have hc := hsat.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
  have hres :=
    (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
  let u := canonicalBlockOddCore n k
  have hu : u = 16 * (u / 16) + 11 := by
    have := Nat.mod_add_div u 16
    omega
  rw [show k + 2 = k + 1 + 1 by omega, hsucc, hnext, hv]
  norm_num
  dsimp [u] at hu hres ⊢
  rw [hc]
  omega

/-- The modulo-sixteen obstruction splits into the two possible modulo-thirty-
two continuation classes. -/
theorem core_mod_thirtyTwo_eq_eleven_or_twentySeven
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k) :
    canonicalBlockOddCore n k % 32 = 11 ∨
      canonicalBlockOddCore n k % 32 = 27 := by
  have hres :=
    (canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
      n k).1 h |>.2.2.1
  omega

/-- In residue class eleven modulo thirty-two, the following block again has
length one. -/
theorem followingBlockLength_eq_one_of_core_mod_thirtyTwo_eq_eleven
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
    (hres : canonicalBlockOddCore n k % 32 = 11) :
    canonicalBlockLength n (k + 2) = 1 := by
  let u := canonicalBlockOddCore n k
  have hu : u = 32 * (u / 32) + 11 := by
    have := Nat.mod_add_div u 32
    omega
  rw [canonicalBlockLength_eq_v2_startState_add_one, h.followingStartState_eq]
  have hstart : (27 * u - 1) / 8 + 1 = 108 * (u / 32) + 38 := by
    omega
  dsimp [u] at hu hstart hres ⊢
  rw [hstart]
  have heven : (108 * (canonicalBlockOddCore n k / 32) + 38) % 2 = 0 := by
    omega
  have hpos : 0 < 108 * (canonicalBlockOddCore n k / 32) + 38 := by omega
  have hhalfodd :
      ((108 * (canonicalBlockOddCore n k / 32) + 38) / 2) % 2 = 1 := by
    omega
  rw [v2_step_of_even _ heven hpos, v2_odd _ hhalfodd]

/-- In residue class twenty-seven modulo thirty-two, the following block has
length at least two.  This is the first persistence branch not settled by the
local length-one grammar. -/
theorem two_le_followingBlockLength_of_core_mod_thirtyTwo_eq_twentySeven
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
    (hres : canonicalBlockOddCore n k % 32 = 27) :
    2 ≤ canonicalBlockLength n (k + 2) := by
  let u := canonicalBlockOddCore n k
  have hu : u = 32 * (u / 32) + 27 := by
    have := Nat.mod_add_div u 32
    omega
  rw [canonicalBlockLength_eq_v2_startState_add_one, h.followingStartState_eq]
  have hstart : (27 * u - 1) / 8 + 1 = 108 * (u / 32) + 92 := by
    omega
  dsimp [u] at hu hstart hres ⊢
  rw [hstart]
  apply (two_le_v2_iff_four_dvd (by omega)).2
  exact ⟨27 * (canonicalBlockOddCore n k / 32) + 23, by ring⟩

/-- The length-one modulo-thirty-two continuation cannot itself be saturated,
because saturation requires canonical length two. -/
theorem not_following_saturated_of_core_mod_thirtyTwo_eq_eleven
    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneBalancedCarrySuccessor n k)
    (hres : canonicalBlockOddCore n k % 32 = 11) :
    ¬ CanonicalSaturatedBorderBlock n (k + 2) := by
  intro hsaturated
  have hOne := h.followingBlockLength_eq_one_of_core_mod_thirtyTwo_eq_eleven hres
  rw [hsaturated.length_eq_two] at hOne
  omega

end CanonicalLengthOneBalancedCarrySuccessor

/-!
The modulo-thirty-two grammar is exact for one further block.  The class
`u % 32 = 27` only yields following length at least two; deciding whether that
block is saturated also requires its claim count and terminal valuation.
Those are not determined by the predecessor residue currently exposed by the
API.  A modulo-64 arithmetic split alone therefore cannot establish or exclude
persistence without a new claim-transport theorem.
-/

/-! ## Abstract nonduplicating dyadic carrier

This section realizes the numerical half-budget as two disjoint `Fin` images.
The low two points carry the preceding saturated unit; the positive successor
demand is shifted into the upper half.  These are abstract potential slots.
They are not orbit indices, binary bit positions, or upper-boundary resources.
-/

/-- The positive nonsaturated demand embeds into the upper half of its abstract
block budget. -/
noncomputable def abstractDyadicDemandEmbeddingUpperHalf
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    CanonicalAbstractDyadicDemandCarrier n k ↪
      CanonicalAbstractDyadicBudgetCarrier n k where
  toFun i := by
    let half := 2 ^ (canonicalBlockLength n k - 2)
    have hdemand :=
      intToNat_endpointAccountingTerm_mul_two_pow_depth_le_two_pow_length_sub_two
        hpos hnot
    have hL :=
      three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
        hpos hnot
    refine ⟨half + i.val, ?_⟩
    rw [show canonicalBlockLength n k - 1 =
        (canonicalBlockLength n k - 2) + 1 by omega, pow_succ]
    omega
  inj' := by
    intro i j hij
    have hval := congrArg Fin.val hij
    change 2 ^ (canonicalBlockLength n k - 2) + i.val =
      2 ^ (canonicalBlockLength n k - 2) + j.val at hval
    exact Fin.ext (Nat.add_left_cancel hval)

/-- The preceding saturated mass-two unit occupies the first two abstract
slots of a positive nonsaturated successor budget. -/
noncomputable def abstractSaturatedUnitEmbeddingLowerHalf
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n (k + 1))
    (hnot : ¬ CanonicalSaturatedBorderBlock n (k + 1)) :
    Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1) where
  toFun i := by
    have hL :=
      three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
        hpos hnot
    refine ⟨i.val, ?_⟩
    have hfour : 4 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 1) := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show 2 ≤ canonicalBlockLength n (k + 1) - 1 by omega)
      simpa using this
    omega
  inj' := by
    intro i j hij
    have hval := congrArg Fin.val hij
    change i.val = j.val at hval
    exact Fin.ext hval

/-- The saturated-unit image and successor-demand image are explicitly
disjoint in the abstract successor budget. -/
theorem abstractSaturatedUnitEmbeddingLowerHalf_ne_demandEmbeddingUpperHalf
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n (k + 1))
    (hnot : ¬ CanonicalSaturatedBorderBlock n (k + 1))
    (i : Fin 2) (j : CanonicalAbstractDyadicDemandCarrier n (k + 1)) :
    abstractSaturatedUnitEmbeddingLowerHalf hpos hnot i ≠
      abstractDyadicDemandEmbeddingUpperHalf hpos hnot j := by
  intro heq
  have hL :=
    three_le_canonicalBlockLength_of_endpointAccountingTerm_pos_of_not_saturated
      hpos hnot
  have hhalf : 2 ≤ 2 ^ (canonicalBlockLength n (k + 1) - 2) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (show 1 ≤ canonicalBlockLength n (k + 1) - 2 by omega)
    simpa using this
  have hval := congrArg Fin.val heq
  dsimp [abstractSaturatedUnitEmbeddingLowerHalf,
    abstractDyadicDemandEmbeddingUpperHalf] at hval
  omega

/-! ## Unified local saturated-successor discharge

These constructors package abstract dyadic budget embeddings only.  They do
not identify the finite slots with orbit bits, do not allocate a global root,
and do not permit summing certificates across time.
-/

/-- Complete local abstract-discharge alternatives for one saturated
predecessor and its immediate successor. -/
inductive CanonicalSaturatedSuccessorAbstractDischarge
    (n : OddNat) (k : ℕ) : Prop
  | negative
      (successor_neg : endpointAccountingTerm n (k + 1) < 0)
      (combined_nonpos :
        endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0)
  | zero
      (successor_zero : endpointAccountingTerm n (k + 1) = 0)
      (length_ge_two : 2 ≤ canonicalBlockLength n (k + 1))
      (unitEmbedding : Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1))
  | positive
      (successor_pos : 0 < endpointAccountingTerm n (k + 1))
      (successor_nonsaturated : ¬ CanonicalSaturatedBorderBlock n (k + 1))
      (unitEmbedding : Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1))
      (demandEmbedding : CanonicalAbstractDyadicDemandCarrier n (k + 1) ↪
        CanonicalAbstractDyadicBudgetCarrier n (k + 1))
      (images_disjoint : ∀ i j, unitEmbedding i ≠ demandEmbedding j)

/-- Every saturated predecessor has a complete local abstract-discharge
certificate at its immediate successor. -/
theorem CanonicalSaturatedBorderBlock.successorAbstractDischarge
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    CanonicalSaturatedSuccessorAbstractDischarge n k := by
  by_cases hneg : endpointAccountingTerm n (k + 1) < 0
  · exact .negative hneg
      (h.drift_add_successor_drift_nonpos_of_negative hneg)
  by_cases hzero : endpointAccountingTerm n (k + 1) = 0
  · have hL : 2 ≤ canonicalBlockLength n (k + 1) := by
      by_contra hnot
      have hLone : canonicalBlockLength n (k + 1) = 1 := by
        have hLpos := one_le_canonicalBlockLength n (k + 1)
        omega
      have hclaim := h.next_claimCount_eq_zero_of_length_one hLone
      have hv := one_le_canonicalBlockTerminalValuation n (k + 1)
      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
        n (k + 1)
      rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaim, hzero] at hdrift
      omega
    exact .zero hzero hL (abstractZeroSuccessorUnitEmbedding hzero hL)
  · have hpos : 0 < endpointAccountingTerm n (k + 1) := by omega
    have hnot := h.not_succ
    exact .positive hpos hnot
      (abstractSaturatedUnitEmbeddingLowerHalf hpos hnot)
      (abstractDyadicDemandEmbeddingUpperHalf hpos hnot)
      (abstractSaturatedUnitEmbeddingLowerHalf_ne_demandEmbeddingUpperHalf
        hpos hnot)

/-- Length-one successors repay at least the predecessor's scalar unit. -/
theorem CanonicalSaturatedBorderBlock.lengthOne_next_scalar_repayment
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1) :
    canonicalBlockClaimCount n (k + 1) = 0 ∧
      endpointAccountingTerm n (k + 1) ≤ -1 ∧
        endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0 := by
  have hclaim := h.next_claimCount_eq_zero_of_length_one hL
  have hv := one_le_canonicalBlockTerminalValuation n (k + 1)
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
    n (k + 1)
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaim] at hdrift
  rw [h.netDrift_eq_one]
  omega

/-- Residue eleven modulo sixteen gives exact scalar cancellation. -/
theorem CanonicalSaturatedBorderBlock.lengthOne_next_drift_sum_eq_zero_of_mod16_eleven
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1)
    (hres : canonicalBlockOddCore n k % 16 = 11) :
    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) = 0 := by
  have hv :=
    (h.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres
  have hterm : CanonicalLengthOneTerminalOneSuccessor n k := ⟨h, hL, hv⟩
  exact hterm.predecessorDrift_add_successorDrift_eq_zero

/-- Residue three modulo sixteen repays the predecessor with at least one
additional scalar unit. -/
theorem CanonicalSaturatedBorderBlock.lengthOne_next_drift_sum_le_neg_one_of_mod16_three
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : canonicalBlockLength n (k + 1) = 1)
    (hres : canonicalBlockOddCore n k % 16 = 3) :
    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ -1 := by
  have hnext := h.nextDrift_le_neg_two_of_length_one_mod16_three hL hres
  rw [h.netDrift_eq_one]
  omega

/-!
## Actual upper-boundary audit

The existing upper-window API records scalar carries, widths, and eventually
zero statements.  It does not expose a finite carrier of distinct upper-zero
bit positions, nor a finite binary refinement tree whose leaves are consumed
at most once.  Consequently the abstract embeddings above cannot yet be
transported into a nonreusable initial-state resource.  Reusing one scalar
upper-boundary fact for several block budgets would invalidate the accounting.

This is the genuine boundary of the present branch: a future theorem must
define an actual finite upper resource and prove a uniform nonreuse or
multiplicity bound before any global repayment conclusion is sound.
-/

/-!
## Current boundary after the causal depth queue

The fixed-depth causal layer is now stable: proof-independent arrivals and
exact-length service instantiate the generic Lindley queue; queue zero is
equivalent to a source-bearing forward matching; and depthwise unordered
residuals embed by cardinality into the all-depth causal carrier.

The next unresolved resource question is not queue causality.  It is whether
successor slack can charge saturated tokens in the branches excluded by
`intToNat_endpointAccountingTerm_add_one_le_selectedPressureCarrier_card`:

* a zero-drift successor supplies no positive drift image;
* a positive successor of terminal valuation one does not satisfy the
  valuation-at-least-two spare-incidence theorem.

No cross-depth sharing or cross-block repayment theorem follows from the
present carriers.  Those branches require new local structure and must not be
filled by reusing the unordered classical complement.
-/

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
