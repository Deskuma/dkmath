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
  letI : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
    unfold CanonicalActiveSelectedPressureBucketCarrier
    infer_instance
  letI : Fintype {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
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
  letI (d : {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m}) :
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
  letI : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  letI : Fintype (CanonicalSelectedResidualCarrier n q m) := by
    unfold CanonicalSelectedResidualCarrier
    infer_instance
  letI : Fintype (CanonicalPositivePressureAmplitudeCarrier n q m) := by
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
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
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
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
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
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
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
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  letI : Fintype
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
      simpa [e, canonicalSelectedDriftArrivalWindowEquiv] using
        hforward (e.symm claim)
  · rintro ⟨hqm, pay, hinj, hforward⟩
    refine ⟨hqm, fun claim => pay (e claim), ?_, ?_⟩
    · exact hinj.comp e.injective
    · intro claim
      simpa [e, canonicalSelectedDriftArrivalWindowEquiv] using hforward (e claim)

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
  letI : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  letI : Fintype (CanonicalActiveSelectedPressureBucketCarrier n q m d) := by
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
  letI : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  letI : Fintype
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
  letI : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
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
  letI : Fintype
      {k : ℕ // k ∈ canonicalActiveSelectedPressureBlocksAtDepth n q m d} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureBlocksAtDepth n q m d) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  letI (k : {k : ℕ // k ∈
      canonicalActiveSelectedPressureBlocksAtDepth n q m d}) :
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
  letI : Fintype (CanonicalSelectedDriftBucketCarrier n q m d) := by
    unfold CanonicalSelectedDriftBucketCarrier
    infer_instance
  letI : Fintype
      {k : ℕ // k ∈ canonicalExactLengthBlockIndicesAtDepth n q m d} :=
    Fintype.ofFinset (canonicalExactLengthBlockIndicesAtDepth n q m d) (by simp)
  letI : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
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
  letI : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  letI (d : {d : ℕ // d ∈
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
  letI : Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d) :=
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
  letI : Fintype
      {d : ℕ // d ∈ canonicalActiveSelectedPressureDepthSupport n q m} :=
    Fintype.ofFinset (canonicalActiveSelectedPressureDepthSupport n q m) (by simp)
  letI (d : {d : ℕ // d ∈
      canonicalActiveSelectedPressureDepthSupport n q m}) :
      Fintype (CanonicalActualSelectedDriftResidualCarrier n q m d.val) :=
    Fintype.ofFinset (canonicalActualSelectedDriftResidualFinset n q m d.val) (by simp)
  letI : Fintype (CanonicalAllDepthActualSelectedDriftResidualCarrier n q m) := by
    unfold CanonicalAllDepthActualSelectedDriftResidualCarrier
    infer_instance
  letI : Fintype (CanonicalAllDepthSelectedDriftCausalQueueCarrier n q m) := by
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
  letI : Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k) (by simp)
  letI : Fintype
      {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k} //
        i ∈ canonicalSelectedDriftSpareCarrier n k} :=
    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n k) (by simp)
  apply Classical.choice
  apply Function.Embedding.nonempty_iff_card_le.mpr
  rw [Fintype.card_fin, Fintype.card_coe]
  exact Finset.one_le_card.mpr
    (canonicalSelectedDriftSpareCarrier_nonempty hpos hnot hv)

/-! ## Exact no-spare classes -/

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

/-- Tight positive valuation-one blocks are precisely the candidate class in
which selected drift consumes every selected incidence. -/
def CanonicalTightValuationOnePositiveBlock
    (n : OddNat) (k : ℕ) : Prop :=
  0 < endpointAccountingTerm n k ∧
    ¬ CanonicalSaturatedBorderBlock n k ∧
      canonicalBlockTerminalValuation n k = 1 ∧
        canonicalBlockClaimCount n k = canonicalBlockLength n k - 1

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
