/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass"

namespace DkMath.Collatz

/-!
# Signed mass of open canonical excursions

This module keeps the ordinary signed interval sum visible.  Positive and
negative masses are nonnegative integer sums, so their difference loses no
signed information.  No future queue zero is assumed.
-/

/-- Sum of positive drift parts on the inclusive block interval `q..m`. -/
noncomputable def canonicalPositiveDriftMass
    (n : OddNat) (q m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc q m, max (endpointAccountingTerm n k) 0

/-- Sum of magnitudes of negative drift parts on `q..m`. -/
noncomputable def canonicalNegativeDriftMass
    (n : OddNat) (q m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc q m, max (-endpointAccountingTerm n k) 0

/-- Dynamic selected-depth pressure carried by positive-drift blocks. -/
noncomputable def canonicalDynamicPressureMass
    (n : OddNat) (q m : ℕ) : ℤ :=
  ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
    blockPressureContributionInt n k (canonicalDynamicPressureDepth n k)

/-- Number of saturated unit-drift tokens on the inclusive interval `q..m`. -/
noncomputable def canonicalSaturatedTokenCount
    (n : OddNat) (q m : ℕ) : ℕ :=
  (canonicalSaturatedBlockIndices n q m).card

/-- The positive mass is nonnegative. -/
theorem canonicalPositiveDriftMass_nonneg
    (n : OddNat) (q m : ℕ) :
    0 ≤ canonicalPositiveDriftMass n q m := by
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- The negative mass is nonnegative. -/
theorem canonicalNegativeDriftMass_nonneg
    (n : OddNat) (q m : ℕ) :
    0 ≤ canonicalNegativeDriftMass n q m := by
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Pointwise positive-minus-negative decomposition of signed drift. -/
private theorem endpointAccountingTerm_eq_positivePart_sub_negativePart
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      max (endpointAccountingTerm n k) 0 -
        max (-endpointAccountingTerm n k) 0 := by
  by_cases h : 0 ≤ endpointAccountingTerm n k
  · rw [max_eq_left h, max_eq_right (by omega)]
    omega
  · have hneg : endpointAccountingTerm n k < 0 := by omega
    rw [max_eq_right (by omega), max_eq_left (by omega)]
    omega

/-- Every inclusive drift window is exactly positive mass minus negative
mass. -/
theorem canonicalWindowDriftInt_eq_positiveMass_sub_negativeMass
    (n : OddNat) (q m : ℕ) :
    canonicalWindowDriftInt n q m =
      canonicalPositiveDriftMass n q m - canonicalNegativeDriftMass n q m := by
  unfold canonicalWindowDriftInt canonicalPositiveDriftMass canonicalNegativeDriftMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact endpointAccountingTerm_eq_positivePart_sub_negativePart n k

/-- Positive mass is the ordinary sum over exactly the positive-drift block
indices. -/
theorem canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices
    (n : OddNat) (q m : ℕ) :
    canonicalPositiveDriftMass n q m =
      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        endpointAccountingTerm n k := by
  classical
  unfold canonicalPositiveDriftMass canonicalPositiveDriftBlockIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hpos : 0 < endpointAccountingTerm n k
  · simp [hpos, max_eq_left (le_of_lt hpos)]
  · have hnonpos : endpointAccountingTerm n k ≤ 0 := by omega
    simp [hpos, max_eq_right hnonpos]

/-- On an open positive excursion the ending queue is the exact signed mass
difference from its last-zero start. -/
theorem CanonicalOpenPositiveQueueExcursion.queue_eq_positiveMass_sub_negativeMass
    {n : OddNat} {q m : ℕ}
    (h : CanonicalOpenPositiveQueueExcursion n q m) :
    (canonicalOutstandingClaimQueue n m : ℤ) =
      canonicalPositiveDriftMass n q m - canonicalNegativeDriftMass n q m := by
  rw [h.queue_eq_windowDrift,
    canonicalWindowDriftInt_eq_positiveMass_sub_negativeMass]

/-- Primary open-excursion resource inequality.  Positive drift is paid by
dynamic pressure except for one explicit token per saturated block. -/
theorem CanonicalOpenPositiveQueueExcursion.queue_add_negativeMass_le_pressure_add_saturatedCard
    {n : OddNat} {q m : ℕ}
    (h : CanonicalOpenPositiveQueueExcursion n q m) :
    (canonicalOutstandingClaimQueue n m : ℤ) +
        canonicalNegativeDriftMass n q m ≤
      canonicalDynamicPressureMass n q m +
        (canonicalSaturatedBlockIndices n q m).card := by
  have hmass := h.queue_eq_positiveMass_sub_negativeMass
  have hpressure := sum_positiveDrift_le_dynamicPressureMass_add_saturatedCard n q m
  rw [← canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices] at hpressure
  unfold canonicalDynamicPressureMass
  omega

/-- Named-token-count form of the primary open-excursion resource
inequality. -/
theorem CanonicalOpenPositiveQueueExcursion.queue_add_negativeMass_le_pressure_add_saturated
    {n : OddNat} {q m : ℕ}
    (h : CanonicalOpenPositiveQueueExcursion n q m) :
    (canonicalOutstandingClaimQueue n m : ℤ) +
        canonicalNegativeDriftMass n q m ≤
      canonicalDynamicPressureMass n q m +
        canonicalSaturatedTokenCount n q m := by
  simpa [canonicalSaturatedTokenCount] using
    h.queue_add_negativeMass_le_pressure_add_saturatedCard

/-! ## Disjoint saturated-successor partition -/

/-- Saturated tokens immediately cancelled by a negative successor. -/
noncomputable def canonicalSaturatedNegativeSuccessorIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalSaturatedBlockIndices n q m).filter fun k =>
    endpointAccountingTerm n (k + 1) < 0

/-- Remaining saturated tokens with an actual spare selected incidence in the
successor block.  Negative successors are assigned to the preceding class. -/
noncomputable def canonicalSaturatedSpareSuccessorIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ := by
  classical
  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
      CanonicalSuccessorSpareAvailable n (k + 1)

/-- Remaining zero-rigid saturated successor tokens. -/
noncomputable def canonicalSaturatedZeroRigidSuccessorIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ := by
  classical
  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
      ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
        CanonicalZeroCarrierBalancedBorderBlock n (k + 1)

/-- Remaining tight-positive-rigid saturated successor tokens. -/
noncomputable def canonicalSaturatedTightRigidSuccessorIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ := by
  classical
  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
      ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
        CanonicalTightValuationOnePositiveBlock n (k + 1)

@[simp] theorem mem_canonicalSaturatedNegativeSuccessorIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalSaturatedNegativeSuccessorIndices n q m ↔
      k ∈ canonicalSaturatedBlockIndices n q m ∧
        endpointAccountingTerm n (k + 1) < 0 := by
  simp [canonicalSaturatedNegativeSuccessorIndices]

@[simp] theorem mem_canonicalSaturatedSpareSuccessorIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalSaturatedSpareSuccessorIndices n q m ↔
      k ∈ canonicalSaturatedBlockIndices n q m ∧
        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
          CanonicalSuccessorSpareAvailable n (k + 1) := by
  classical
  rw [canonicalSaturatedSpareSuccessorIndices, Finset.mem_filter]

@[simp] theorem mem_canonicalSaturatedZeroRigidSuccessorIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalSaturatedZeroRigidSuccessorIndices n q m ↔
      k ∈ canonicalSaturatedBlockIndices n q m ∧
        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
          ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
            CanonicalZeroCarrierBalancedBorderBlock n (k + 1) := by
  classical
  rw [canonicalSaturatedZeroRigidSuccessorIndices, Finset.mem_filter]

@[simp] theorem mem_canonicalSaturatedTightRigidSuccessorIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalSaturatedTightRigidSuccessorIndices n q m ↔
      k ∈ canonicalSaturatedBlockIndices n q m ∧
        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
          ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
            CanonicalTightValuationOnePositiveBlock n (k + 1) := by
  classical
  rw [canonicalSaturatedTightRigidSuccessorIndices, Finset.mem_filter]

/-- The four priority classes exhaust all saturated tokens in the interval. -/
theorem canonicalSaturatedSuccessorIndices_union_eq
    (n : OddNat) (q m : ℕ) :
    canonicalSaturatedNegativeSuccessorIndices n q m ∪
        canonicalSaturatedSpareSuccessorIndices n q m ∪
          canonicalSaturatedZeroRigidSuccessorIndices n q m ∪
            canonicalSaturatedTightRigidSuccessorIndices n q m =
      canonicalSaturatedBlockIndices n q m := by
  classical
  apply Finset.Subset.antisymm
  · intro k hk
    simp only [Finset.mem_union] at hk
    rcases hk with ((hk | hk) | hk) | hk
    · exact (mem_canonicalSaturatedNegativeSuccessorIndices.mp hk).1
    · exact (mem_canonicalSaturatedSpareSuccessorIndices.mp hk).1
    · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hk).1
    · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hk).1
  · intro k hk
    have hs := (mem_canonicalSaturatedBlockIndices.mp hk).2
    rcases hs.successor_negative_or_spare_or_rigid with
      hneg | hspare | hzero | htight
    · simp [hk, hneg]
    · by_cases hneg : endpointAccountingTerm n (k + 1) < 0
      · simp [hk, hneg]
      · simp [hk, hneg, hspare]
    · have hzeroDrift : endpointAccountingTerm n (k + 1) = 0 := hzero.1
      have hnospare : ¬ CanonicalSuccessorSpareAvailable n (k + 1) := by
        intro hspare
        have hempty := hzero.2
        unfold CanonicalSuccessorSpareAvailable at hspare
        rcases hspare with ⟨i, _hi⟩
        let : IsEmpty {i : ℕ //
            i ∈ canonicalSelectedPressureCarrier n (k + 1)} := by
          rw [hempty]
          infer_instance
        exact isEmptyElim i
      simp [hk, hzeroDrift, hnospare, hzero]
    · have hpos := htight.1
      have hnospare : ¬ CanonicalSuccessorSpareAvailable n (k + 1) := by
        unfold CanonicalSuccessorSpareAvailable
        rw [htight.exact_data.2.2.2.2]
        exact Finset.not_nonempty_empty
      simp [hk, show ¬ endpointAccountingTerm n (k + 1) < 0 by omega,
        hnospare, htight]

/-- Negative-successor and spare-successor token classes are disjoint. -/
theorem canonicalSaturatedNegative_disjoint_spare
    (n : OddNat) (q m : ℕ) :
    Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
      (canonicalSaturatedSpareSuccessorIndices n q m) := by
  rw [Finset.disjoint_left]
  intro k hneg hspare
  exact (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.1
    (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2

/-- A negative successor numerically cancels the saturated predecessor's unit:
the pair contributes at most zero. -/
theorem canonicalSaturatedNegativeSuccessor_unit_add_term_nonpos
    {n : OddNat} {q m k : ℕ}
    (hk : k ∈ canonicalSaturatedNegativeSuccessorIndices n q m) :
    (1 : ℤ) + endpointAccountingTerm n (k + 1) ≤ 0 := by
  have hneg := (mem_canonicalSaturatedNegativeSuccessorIndices.mp hk).2
  omega

/-- The negative class is disjoint from both rigid residual classes. -/
theorem canonicalSaturatedNegative_disjoint_rigid
    (n : OddNat) (q m : ℕ) :
    Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
        (canonicalSaturatedZeroRigidSuccessorIndices n q m) ∧
      Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
        (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
  constructor <;> rw [Finset.disjoint_left] <;> intro k hneg hrigid
  · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hrigid).2.1
      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2
  · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hrigid).2.1
      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2

/-- The spare class is disjoint from both rigid residual classes. -/
theorem canonicalSaturatedSpare_disjoint_rigid
    (n : OddNat) (q m : ℕ) :
    Disjoint (canonicalSaturatedSpareSuccessorIndices n q m)
        (canonicalSaturatedZeroRigidSuccessorIndices n q m) ∧
      Disjoint (canonicalSaturatedSpareSuccessorIndices n q m)
        (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
  constructor <;> rw [Finset.disjoint_left] <;> intro k hspare hrigid
  · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hrigid).2.2.1
      (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.2
  · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hrigid).2.2.1
      (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.2

/-- The zero-rigid and tight-positive-rigid residual classes are disjoint. -/
theorem canonicalSaturatedZeroRigid_disjoint_tightRigid
    (n : OddNat) (q m : ℕ) :
    Disjoint (canonicalSaturatedZeroRigidSuccessorIndices n q m)
      (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
  rw [Finset.disjoint_left]
  intro k hzero htight
  have hz :=
    (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hzero).2.2.2.1
  have hp :=
    (mem_canonicalSaturatedTightRigidSuccessorIndices.mp htight).2.2.2.1
  omega

/-- Exact visible residual after negative and spare successor modes are
separated.  Neither rigid family is hidden in an abstract potential. -/
noncomputable def canonicalRigidSaturatedResidualCount
    (n : OddNat) (q m : ℕ) : ℕ :=
  (canonicalSaturatedZeroRigidSuccessorIndices n q m).card +
    (canonicalSaturatedTightRigidSuccessorIndices n q m).card

/-- The priority successor classification gives an exact cardinal
decomposition of all saturated tokens. -/
theorem canonicalSaturatedTokenCount_eq_successorClassCounts
    (n : OddNat) (q m : ℕ) :
    canonicalSaturatedTokenCount n q m =
      (canonicalSaturatedNegativeSuccessorIndices n q m).card +
        (canonicalSaturatedSpareSuccessorIndices n q m).card +
          canonicalRigidSaturatedResidualCount n q m := by
  classical
  let N := canonicalSaturatedNegativeSuccessorIndices n q m
  let S := canonicalSaturatedSpareSuccessorIndices n q m
  let Z := canonicalSaturatedZeroRigidSuccessorIndices n q m
  let T := canonicalSaturatedTightRigidSuccessorIndices n q m
  have hNS : Disjoint N S := canonicalSaturatedNegative_disjoint_spare n q m
  have hNZ : Disjoint N Z := (canonicalSaturatedNegative_disjoint_rigid n q m).1
  have hNT : Disjoint N T := (canonicalSaturatedNegative_disjoint_rigid n q m).2
  have hSZ : Disjoint S Z := (canonicalSaturatedSpare_disjoint_rigid n q m).1
  have hST : Disjoint S T := (canonicalSaturatedSpare_disjoint_rigid n q m).2
  have hZT : Disjoint Z T := canonicalSaturatedZeroRigid_disjoint_tightRigid n q m
  have hN_SZT : Disjoint N (S ∪ (Z ∪ T)) := by
    rw [Finset.disjoint_left]
    intro x hxN hx
    simp only [Finset.mem_union] at hx
    rcases hx with hxS | hxZ | hxT
    · exact Finset.disjoint_left.mp hNS hxN hxS
    · exact Finset.disjoint_left.mp hNZ hxN hxZ
    · exact Finset.disjoint_left.mp hNT hxN hxT
  have hS_ZT : Disjoint S (Z ∪ T) := by
    rw [Finset.disjoint_left]
    intro x hxS hx
    rcases Finset.mem_union.mp hx with hxZ | hxT
    · exact Finset.disjoint_left.mp hSZ hxS hxZ
    · exact Finset.disjoint_left.mp hST hxS hxT
  have hunion : N ∪ (S ∪ (Z ∪ T)) = canonicalSaturatedBlockIndices n q m := by
    simpa [N, S, Z, T, Finset.union_assoc] using
      canonicalSaturatedSuccessorIndices_union_eq n q m
  rw [canonicalSaturatedTokenCount, ← hunion]
  calc
    (N ∪ (S ∪ (Z ∪ T))).card = N.card + (S ∪ (Z ∪ T)).card :=
      Finset.card_union_of_disjoint hN_SZT
    _ = N.card + (S.card + (Z ∪ T).card) := by
      rw [Finset.card_union_of_disjoint hS_ZT]
    _ = N.card + (S.card + (Z.card + T.card)) := by
      rw [Finset.card_union_of_disjoint hZT]
    _ = (canonicalSaturatedNegativeSuccessorIndices n q m).card +
          (canonicalSaturatedSpareSuccessorIndices n q m).card +
            canonicalRigidSaturatedResidualCount n q m := by
      simp only [canonicalRigidSaturatedResidualCount, N, S, Z, T]
      omega

/-!
The successor partition deliberately observes blocks `q+1..m+1`.  Therefore
the negative class containing `k = m` is cancelled by drift at `m+1`, outside
the present open-excursion mass interval `q..m`.  Likewise its spare incidence
lives in the one-step successor horizon.  A theorem replacing every saturated
token in the current-window inequality by current-window negative mass or a
selected carrier would silently spend a future resource.  The next honest
strengthening must either:

* restrict charging to `k < m` and retain the terminal saturated token as a
  separate boundary residual; or
* extend the accounting window through `m+1` and prove the corresponding queue
  transport identity.

Until one of these temporal contracts is chosen, the exact partition,
pointwise cancellation, and successor-spare injection below are the public
finite certificates; no stronger contribution-preserving inequality is
claimed.
-/

/-! ## Global successor-spare charging -/

/-- All actual spare selected incidences in successor blocks of `q..m`, with
the successor block coordinate retained to prevent temporal reuse. -/
noncomputable def CanonicalGlobalSuccessorSpareCarrier
    (n : OddNat) (q m : ℕ) : Type :=
  Σ j : {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)},
    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.1} //
      i ∈ canonicalSelectedDriftSpareCarrier n j.1}

/-- Each spare-class saturated token chooses one actual incidence in its own
successor block.  The retained successor coordinate makes the map injective. -/
noncomputable def canonicalSaturatedSpareTokenEmbedding
    (n : OddNat) (q m : ℕ) :
    {k : ℕ // k ∈ canonicalSaturatedSpareSuccessorIndices n q m} ↪
      CanonicalGlobalSuccessorSpareCarrier n q m where
  toFun k := by
    have hk := mem_canonicalSaturatedSpareSuccessorIndices.mp k.2
    have hkIcc := (mem_canonicalSaturatedBlockIndices.mp hk.1).1
    let e := oneEmbedding_successorSpareCarrier hk.2.2
    exact ⟨⟨k.1 + 1, Finset.mem_Icc.mpr ⟨by
      exact Nat.add_le_add_right (Finset.mem_Icc.mp hkIcc).1 1
    , by
      exact Nat.add_le_add_right (Finset.mem_Icc.mp hkIcc).2 1⟩⟩, e 0⟩
  inj' := by
    intro a b hab
    have hindex := congrArg (fun z => z.1.1) hab
    change a.1 + 1 = b.1 + 1 at hindex
    apply Subtype.ext
    omega

/-- No spare incidence is reused for two saturated tokens. -/
theorem card_canonicalSaturatedSpareSuccessorIndices_le_globalCarrier
    (n : OddNat) (q m : ℕ) :
    (canonicalSaturatedSpareSuccessorIndices n q m).card ≤
      Nat.card (CanonicalGlobalSuccessorSpareCarrier n q m) := by
  classical
  let : Fintype {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)} :=
    Fintype.ofFinset (Finset.Icc (q + 1) (m + 1)) (by simp)
  let : ∀ j : {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)},
      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.1} //
        i ∈ canonicalSelectedDriftSpareCarrier n j.1} := fun j =>
    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n j.1) (by simp)
  let : Fintype (CanonicalGlobalSuccessorSpareCarrier n q m) := by
    unfold CanonicalGlobalSuccessorSpareCarrier
    infer_instance
  have hcard := Nat.card_le_card_of_injective
    (canonicalSaturatedSpareTokenEmbedding n q m)
    (canonicalSaturatedSpareTokenEmbedding n q m).injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

end DkMath.Collatz
