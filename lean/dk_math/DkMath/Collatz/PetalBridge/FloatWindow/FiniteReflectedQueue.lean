/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue"

namespace DkMath.Collatz

/-!
# Generic finite reflected queue

This module is independent of orbit and Collatz definitions.  It separates a
causal, recursively reflected queue from the unordered positive part of total
signed balance.  Arrivals and service are anonymous natural-number counts.
-/

/-- Reflected queue started immediately before absolute index `q`. -/
def finiteReflectedQueueFrom
    (arrivals service : ℕ → ℕ) (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      (finiteReflectedQueueFrom arrivals service q t + arrivals (q + t)) -
        service (q + t)

/-- Terminal queue after processing every index in the closed window `q..m`.
The intended public use supplies `q ≤ m`. -/
def finiteReflectedQueueOn
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  finiteReflectedQueueFrom arrivals service q (m - q + 1)

/-- Total closed-interval queue.  Unlike `finiteReflectedQueueOn`, this wrapper
treats `m < q` as the empty window and therefore processes no index. -/
def finiteReflectedQueueOnIcc
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  if q ≤ m then finiteReflectedQueueOn arrivals service q m else 0

/-- On a nonempty closed interval, the total wrapper is the compatibility
queue. -/
theorem finiteReflectedQueueOnIcc_eq_reflectedQueueOn
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOnIcc arrivals service q m =
      finiteReflectedQueueOn arrivals service q m := by
  simp [finiteReflectedQueueOnIcc, hqm]

/-- A reversed closed interval is an empty queue window. -/
theorem finiteReflectedQueueOnIcc_eq_zero_of_lt
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hmq : m < q) :
    finiteReflectedQueueOnIcc arrivals service q m = 0 := by
  simp [finiteReflectedQueueOnIcc, Nat.not_le.mpr hmq]

/-- Signed arrivals-minus-service balance on a closed finite window. -/
def finiteSignedWindowBalance
    (arrivals service : ℕ → ℕ) (t m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc t m, ((arrivals k : ℤ) - service k)

@[simp] theorem finiteReflectedQueueFrom_zero
    (arrivals service : ℕ → ℕ) (q : ℕ) :
    finiteReflectedQueueFrom arrivals service q 0 = 0 :=
  rfl

/-- Causal successor equation in local time. -/
theorem finiteReflectedQueueFrom_succ
    (arrivals service : ℕ → ℕ) (q t : ℕ) :
    finiteReflectedQueueFrom arrivals service q (t + 1) =
      (finiteReflectedQueueFrom arrivals service q t + arrivals (q + t)) -
        service (q + t) :=
  rfl

/-- Nat reflection is the nonnegative part of the corresponding signed step. -/
theorem finiteReflectedQueueFrom_succ_eq_intToNat
    (arrivals service : ℕ → ℕ) (q t : ℕ) :
    finiteReflectedQueueFrom arrivals service q (t + 1) =
      Int.toNat ((finiteReflectedQueueFrom arrivals service q t : ℤ) +
        arrivals (q + t) - service (q + t)) := by
  rw [finiteReflectedQueueFrom_succ]
  omega

/-- A singleton signed window is one arrivals-minus-service term. -/
theorem finiteSignedWindowBalance_self
    (arrivals service : ℕ → ℕ) (m : ℕ) :
    finiteSignedWindowBalance arrivals service m m =
      (arrivals m : ℤ) - service m := by
  simp [finiteSignedWindowBalance]

/-- Extending a nonempty-right window appends its terminal term. -/
theorem finiteSignedWindowBalance_succ
    (arrivals service : ℕ → ℕ) {t m : ℕ} (ht : t ≤ m + 1) :
    finiteSignedWindowBalance arrivals service t (m + 1) =
      (if t ≤ m then finiteSignedWindowBalance arrivals service t m else 0) +
        ((arrivals (m + 1) : ℤ) - service (m + 1)) := by
  by_cases htm : t ≤ m
  · rw [ite_eq_left htm]
    unfold finiteSignedWindowBalance
    have hIcc : Finset.Icc t (m + 1) = insert (m + 1) (Finset.Icc t m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp)]
    ring
  · have hteq : t = m + 1 := by omega
    subst t
    simp [finiteSignedWindowBalance]

/-- Right extension equation for a nonempty terminal queue window. -/
theorem finiteReflectedQueueOn_succ
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q (m + 1) =
      (finiteReflectedQueueOn arrivals service q m + arrivals (m + 1)) -
        service (m + 1) := by
  unfold finiteReflectedQueueOn
  have hstep : m + 1 - q + 1 = (m - q + 1) + 1 := by omega
  have hindex : q + (m - q + 1) = m + 1 := by omega
  rw [hstep, finiteReflectedQueueFrom_succ]
  rw [hindex]

/-- Integer-positive-part form of right extension. -/
theorem finiteReflectedQueueOn_succ_eq_intToNat
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q (m + 1) =
      Int.toNat ((finiteReflectedQueueOn arrivals service q m : ℤ) +
        arrivals (m + 1) - service (m + 1)) := by
  rw [finiteReflectedQueueOn_succ arrivals service hqm]
  omega

/-- A singleton terminal window is one reflected arrivals/service step. -/
theorem finiteReflectedQueueOn_self
    (arrivals service : ℕ → ℕ) (q : ℕ) :
    finiteReflectedQueueOn arrivals service q q =
      arrivals q - service q := by
  simp [finiteReflectedQueueOn, finiteReflectedQueueFrom]

/-- Every suffix positive balance is bounded by the causal terminal queue. -/
theorem intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
    (arrivals service : ℕ → ℕ) {q t m : ℕ}
    (hqt : q ≤ t) (htm : t ≤ m) :
    Int.toNat (finiteSignedWindowBalance arrivals service t m) ≤
      finiteReflectedQueueOn arrivals service q m := by
  induction m generalizing q t with
  | zero =>
      have hq : q = 0 := by omega
      have ht : t = 0 := by omega
      subst q
      subst t
      rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]
      omega
  | succ m ih =>
      by_cases htm' : t ≤ m
      · rw [finiteSignedWindowBalance_succ arrivals service (by omega), ite_eq_left htm']
        rw [finiteReflectedQueueOn_succ arrivals service (by omega)]
        have hprev := ih hqt htm'
        have hself := Int.self_le_toNat
          (finiteSignedWindowBalance arrivals service t m)
        omega
      · have ht : t = m + 1 := by omega
        subst t
        rw [finiteSignedWindowBalance_self]
        by_cases hqeq : q = m + 1
        · subst q
          rw [finiteReflectedQueueOn_self]
          omega
        · rw [finiteReflectedQueueOn_succ arrivals service (by omega)]
          omega

/-- A positive terminal queue is attained by one suffix positive balance. -/
theorem finiteReflectedQueueOn_eq_zero_or_exists_suffix
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q m = 0 ∨
      (0 < finiteReflectedQueueOn arrivals service q m ∧
        ∃ t ∈ Finset.Icc q m,
          finiteReflectedQueueOn arrivals service q m =
            Int.toNat (finiteSignedWindowBalance arrivals service t m)) := by
  induction m generalizing q with
  | zero =>
      have hq : q = 0 := by omega
      subst q
      by_cases hzero : finiteReflectedQueueOn arrivals service 0 0 = 0
      · exact Or.inl hzero
      · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, 0, by simp,
          by rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]; omega⟩
  | succ m ih =>
      by_cases hqeq : q = m + 1
      · subst q
        by_cases hzero : finiteReflectedQueueOn arrivals service (m + 1) (m + 1) = 0
        · exact Or.inl hzero
        · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, m + 1, by simp,
            by rw [finiteSignedWindowBalance_self, finiteReflectedQueueOn_self]; omega⟩
      · have hqm' : q ≤ m := by omega
        by_cases hzero : finiteReflectedQueueOn arrivals service q (m + 1) = 0
        · exact Or.inl hzero
        · refine Or.inr ⟨Nat.pos_of_ne_zero hzero, ?_⟩
          rcases ih hqm' with hold | ⟨holdPos, t, ht, holdWitness⟩
          · refine ⟨m + 1, by simp [hqm], ?_⟩
            rw [finiteSignedWindowBalance_self,
              finiteReflectedQueueOn_succ arrivals service hqm', hold]
            omega
          · have htBounds := Finset.mem_Icc.mp ht
            refine ⟨t, Finset.mem_Icc.mpr ⟨htBounds.1, by omega⟩, ?_⟩
            rw [finiteReflectedQueueOn_succ_eq_intToNat arrivals service hqm',
              finiteSignedWindowBalance_succ arrivals service (by omega),
              ite_eq_left htBounds.2]
            have hnonneg : 0 ≤ finiteSignedWindowBalance arrivals service t m := by
              by_contra hneg
              have hz : Int.toNat
                  (finiteSignedWindowBalance arrivals service t m) = 0 :=
                Int.toNat_of_nonpos (by omega)
              omega
            have hcast : (finiteReflectedQueueOn arrivals service q m : ℤ) =
                finiteSignedWindowBalance arrivals service t m := by
              rw [holdWitness, Int.ofNat_toNat, max_eq_left hnonneg]
            rw [hcast]
            congr 1
            ring

/-- Maximum positive suffix balance in a finite closed window. -/
def finiteReflectedWindowMaximum
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  (Finset.Icc q m).sup fun t =>
    Int.toNat (finiteSignedWindowBalance arrivals service t m)

/-- Lindley reflection identity on a finite closed window. -/
theorem finiteReflectedQueueOn_eq_windowMaximum
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q m =
      finiteReflectedWindowMaximum arrivals service q m := by
  apply le_antisymm
  · rcases finiteReflectedQueueOn_eq_zero_or_exists_suffix
      arrivals service hqm with hzero | ⟨_, t, ht, hqueue⟩
    · simp [hzero]
    · rw [hqueue]
      exact Finset.le_sup (f := fun t =>
        Int.toNat (finiteSignedWindowBalance arrivals service t m)) ht
  · unfold finiteReflectedWindowMaximum
    apply Finset.sup_le
    intro t ht
    exact intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
      arrivals service (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2

/-- Queue zero is exactly nonpositivity of every release-time suffix. -/
theorem finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q m = 0 ↔
      ∀ t ∈ Finset.Icc q m,
        finiteSignedWindowBalance arrivals service t m ≤ 0 := by
  rw [finiteReflectedQueueOn_eq_windowMaximum arrivals service hqm]
  constructor
  · intro hzero t ht
    have hle : Int.toNat (finiteSignedWindowBalance arrivals service t m) ≤ 0 := by
      rw [← hzero]
      unfold finiteReflectedWindowMaximum
      exact Finset.le_sup (f := fun t =>
        Int.toNat (finiteSignedWindowBalance arrivals service t m)) ht
    exact Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
  · intro hall
    apply Nat.eq_zero_of_le_zero
    unfold finiteReflectedWindowMaximum
    apply Finset.sup_le
    intro t ht
    rw [Int.toNat_of_nonpos (hall t ht)]

/-- Total zero characterization, including the empty closed interval. -/
theorem finiteReflectedQueueOnIcc_eq_zero_iff_all_suffix_nonpos
    (arrivals service : ℕ → ℕ) (q m : ℕ) :
    finiteReflectedQueueOnIcc arrivals service q m = 0 ↔
      ∀ t ∈ Finset.Icc q m,
        finiteSignedWindowBalance arrivals service t m ≤ 0 := by
  by_cases hqm : q ≤ m
  · rw [finiteReflectedQueueOnIcc_eq_reflectedQueueOn arrivals service hqm]
    exact finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos
      arrivals service hqm
  · have hempty : Finset.Icc q m = ∅ := by
      exact Finset.Icc_eq_empty hqm
    simp [finiteReflectedQueueOnIcc, hqm, hempty]

/-- Unordered positive part of total balance on the whole window. -/
def finiteUnorderedResidual
    (arrivals service : ℕ → ℕ) (q m : ℕ) : ℕ :=
  Int.toNat (finiteSignedWindowBalance arrivals service q m)

/-- Unordered residual never exceeds the causal reflected queue. -/
theorem finiteUnorderedResidual_le_reflectedQueueOn
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteUnorderedResidual arrivals service q m ≤
      finiteReflectedQueueOn arrivals service q m := by
  exact intToNat_finiteSignedWindowBalance_le_reflectedQueueOn
    arrivals service le_rfl hqm

/-! ## Semantic regression: early service cannot repay future arrivals -/

private def earlyServiceArrival : ℕ → ℕ
  | 1 => 1
  | _ => 0

private def earlyServiceCapacity : ℕ → ℕ
  | 0 => 1
  | _ => 0

theorem earlyService_unorderedResidual_zero :
    finiteUnorderedResidual earlyServiceArrival earlyServiceCapacity 0 1 = 0 := by
  have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
  rw [show finiteUnorderedResidual earlyServiceArrival earlyServiceCapacity 0 1 =
      Int.toNat (finiteSignedWindowBalance earlyServiceArrival
        earlyServiceCapacity 0 1) by rfl]
  unfold finiteSignedWindowBalance
  rw [hIcc]
  norm_num [finiteUnorderedResidual, finiteSignedWindowBalance,
    earlyServiceArrival, earlyServiceCapacity]

theorem earlyService_causalQueue_one :
    finiteReflectedQueueOn earlyServiceArrival earlyServiceCapacity 0 1 = 1 := by
  norm_num [finiteReflectedQueueOn, finiteReflectedQueueFrom,
    earlyServiceArrival, earlyServiceCapacity]

/-! ## Generic finite interval-order Hall layer -/

/-- Arrival units retaining their release block. -/
def FiniteArrivalWindowCarrier
    (arrivals : ℕ → ℕ) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (arrivals k.val)

/-- Service units retaining their availability block. -/
def FiniteServiceWindowCarrier
    (service : ℕ → ℕ) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q m}, Fin (service k.val)

/-- A causal matching sends every claim to a distinct service slot at its own
block or a later block. -/
def FiniteForwardWindowMatching
    (arrivals service : ℕ → ℕ) (q m : ℕ) : Prop :=
  q ≤ m ∧ ∃ pay : FiniteArrivalWindowCarrier arrivals q m →
      FiniteServiceWindowCarrier service q m,
    Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val

/-- Cardinality of the generic arrival carrier. -/
theorem natCard_finiteArrivalWindowCarrier
    (arrivals : ℕ → ℕ) (q m : ℕ) :
    Nat.card (FiniteArrivalWindowCarrier arrivals q m) =
      ∑ k ∈ Finset.Icc q m, arrivals k := by
  unfold FiniteArrivalWindowCarrier
  rw [Nat.card_sigma, Finset.univ_eq_attach]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Finset.sum_attach (Finset.Icc q m) arrivals

/-- Cardinality of the generic service carrier. -/
theorem natCard_finiteServiceWindowCarrier
    (service : ℕ → ℕ) (q m : ℕ) :
    Nat.card (FiniteServiceWindowCarrier service q m) =
      ∑ k ∈ Finset.Icc q m, service k := by
  unfold FiniteServiceWindowCarrier
  rw [Nat.card_sigma, Finset.univ_eq_attach]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Finset.sum_attach (Finset.Icc q m) service

/-- Forward matching forces every release-time suffix Hall inequality. -/
theorem FiniteForwardWindowMatching.to_suffix_sum_le
    {arrivals service : ℕ → ℕ} {q m : ℕ}
    (h : FiniteForwardWindowMatching arrivals service q m) :
    ∀ t ∈ Finset.Icc q m,
      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
        ∑ k ∈ Finset.Icc t m, service k := by
  classical
  rcases h with ⟨_, pay, hpayInjective, hpayForward⟩
  intro t ht
  have hqt := (Finset.mem_Icc.mp ht).1
  let includeClaim : FiniteArrivalWindowCarrier arrivals t m →
      FiniteArrivalWindowCarrier arrivals q m := fun claim =>
    ⟨⟨claim.1.val, Finset.mem_Icc.mpr
      ⟨hqt.trans (Finset.mem_Icc.mp claim.1.property).1,
        (Finset.mem_Icc.mp claim.1.property).2⟩⟩, claim.2⟩
  have includeClaim_injective : Function.Injective includeClaim := by
    intro a b hab
    apply Sigma.ext_iff.mpr
    exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
      (Sigma.ext_iff.mp hab).2⟩
  let suffixPay : FiniteArrivalWindowCarrier arrivals t m →
      FiniteServiceWindowCarrier service t m := fun claim =>
    ⟨⟨(pay (includeClaim claim)).1.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp claim.1.property).1.trans
          (hpayForward (includeClaim claim)),
        (Finset.mem_Icc.mp (pay (includeClaim claim)).1.property).2⟩⟩,
      (pay (includeClaim claim)).2⟩
  have suffixPay_injective : Function.Injective suffixPay := by
    intro a b hab
    apply includeClaim_injective
    apply hpayInjective
    apply Sigma.ext_iff.mpr
    exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
      (Sigma.ext_iff.mp hab).2⟩
  let : Finite (FiniteArrivalWindowCarrier arrivals t m) := by
    unfold FiniteArrivalWindowCarrier
    infer_instance
  let : Finite (FiniteServiceWindowCarrier service t m) := by
    unfold FiniteServiceWindowCarrier
    infer_instance
  have hcard := Nat.card_le_card_of_injective suffixPay suffixPay_injective
  rw [natCard_finiteArrivalWindowCarrier,
    natCard_finiteServiceWindowCarrier] at hcard
  exact hcard

/-- Nested suffix Hall inequalities construct a causal forward matching. -/
theorem finiteForwardWindowMatching_of_suffix_sum_le
    {arrivals service : ℕ → ℕ} {q m : ℕ} (hqm : q ≤ m)
    (hall : ∀ t ∈ Finset.Icc q m,
      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
        ∑ k ∈ Finset.Icc t m, service k) :
    FiniteForwardWindowMatching arrivals service q m := by
  classical
  let Claim := FiniteArrivalWindowCarrier arrivals q m
  let Slot := FiniteServiceWindowCarrier service q m
  let : Finite Claim := by
    dsimp [Claim]
    unfold FiniteArrivalWindowCarrier
    infer_instance
  let : Finite Slot := by
    dsimp [Slot]
    unfold FiniteServiceWindowCarrier
    infer_instance
  let : Fintype Claim := Fintype.ofFinite Claim
  let : Fintype Slot := Fintype.ofFinite Slot
  let eligible : Claim → Slot → Prop := fun claim slot =>
    claim.1.val ≤ slot.1.val
  have hallSubsets : ∀ A : Finset Claim,
      A.card ≤ ({slot : Slot | ∃ claim ∈ A, eligible claim slot} : Finset Slot).card := by
    intro A
    by_cases hA : A.Nonempty
    · let blocks : Finset ℕ := A.image fun claim => claim.1.val
      have hblocks : blocks.Nonempty := hA.image _
      let t := blocks.min' hblocks
      have htBlocks : t ∈ blocks := Finset.min'_mem blocks hblocks
      rcases Finset.mem_image.mp htBlocks with ⟨minClaim, hminClaimA, hminBlock⟩
      have htIcc : t ∈ Finset.Icc q m := by
        rw [← hminBlock]
        exact minClaim.1.property
      have ht_le_claim : ∀ claim ∈ A, t ≤ claim.1.val := by
        intro claim hclaim
        exact Finset.min'_le blocks _
          (Finset.mem_image.mpr ⟨claim, hclaim, rfl⟩)
      let claimsFromT : ↥A → FiniteArrivalWindowCarrier arrivals t m := fun claim =>
        ⟨⟨claim.val.1.val, Finset.mem_Icc.mpr
          ⟨ht_le_claim claim.val claim.property,
            (Finset.mem_Icc.mp claim.val.1.property).2⟩⟩, claim.val.2⟩
      have claimsFromT_injective : Function.Injective claimsFromT := by
        intro a b hab
        apply Subtype.ext
        apply Sigma.ext_iff.mpr
        exact ⟨Subtype.ext (congrArg (fun x => x.1.val) hab),
          (Sigma.ext_iff.mp hab).2⟩
      have hAClaims : A.card ≤ ∑ k ∈ Finset.Icc t m, arrivals k := by
        let : Finite (FiniteArrivalWindowCarrier arrivals t m) := by
          unfold FiniteArrivalWindowCarrier
          infer_instance
        let : Fintype (FiniteArrivalWindowCarrier arrivals t m) :=
          Fintype.ofFinite _
        have hcard := Fintype.card_le_of_injective claimsFromT
          claimsFromT_injective
        rw [← natCard_finiteArrivalWindowCarrier arrivals t m]
        simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
      let slotsToEligible : FiniteServiceWindowCarrier service t m →
          {slot : Slot // ∃ claim ∈ A, eligible claim slot} := fun slot =>
        ⟨⟨⟨slot.1.val, Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp htIcc).1.trans
              (Finset.mem_Icc.mp slot.1.property).1,
            (Finset.mem_Icc.mp slot.1.property).2⟩⟩, slot.2⟩,
          ⟨minClaim, hminClaimA, by
            change minClaim.1.val ≤ slot.1.val
            rw [hminBlock]
            exact (Finset.mem_Icc.mp slot.1.property).1⟩⟩
      have slotsToEligible_injective : Function.Injective slotsToEligible := by
        intro a b hab
        apply Sigma.ext_iff.mpr
        constructor
        · exact Subtype.ext (congrArg (fun x => x.val.1.val) hab)
        · exact (Sigma.ext_iff.mp (congrArg Subtype.val hab)).2
      have hSlotsEligible : (∑ k ∈ Finset.Icc t m, service k) ≤
          ({slot : Slot | ∃ claim ∈ A, eligible claim slot} : Finset Slot).card := by
        let : Finite (FiniteServiceWindowCarrier service t m) := by
          unfold FiniteServiceWindowCarrier
          infer_instance
        let : Fintype (FiniteServiceWindowCarrier service t m) :=
          Fintype.ofFinite _
        have hcard := Fintype.card_le_of_injective slotsToEligible
          slotsToEligible_injective
        rw [← natCard_finiteServiceWindowCarrier service t m]
        rw [Nat.card_eq_fintype_card]
        rw [Fintype.card_subtype] at hcard
        exact hcard
      exact hAClaims.trans ((hall t htIcc).trans hSlotsEligible)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp
  rcases (Fintype.all_card_le_filter_rel_iff_exists_injective eligible).1
      hallSubsets with ⟨pay, hpay, heligible⟩
  exact ⟨hqm, pay, hpay, heligible⟩

/-- Generic interval-order Hall theorem. -/
theorem finiteForwardWindowMatching_iff_suffix_sum_le
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    FiniteForwardWindowMatching arrivals service q m ↔
      ∀ t ∈ Finset.Icc q m,
        (∑ k ∈ Finset.Icc t m, arrivals k) ≤
          ∑ k ∈ Finset.Icc t m, service k := by
  constructor
  · exact FiniteForwardWindowMatching.to_suffix_sum_le
  · exact finiteForwardWindowMatching_of_suffix_sum_le hqm

/-- Signed nonpositivity is equivalent to the natural suffix Hall inequality. -/
theorem finiteSignedWindowBalance_nonpos_iff_sum_le
    (arrivals service : ℕ → ℕ) (t m : ℕ) :
    finiteSignedWindowBalance arrivals service t m ≤ 0 ↔
      (∑ k ∈ Finset.Icc t m, arrivals k) ≤
        ∑ k ∈ Finset.Icc t m, service k := by
  unfold finiteSignedWindowBalance
  rw [Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  omega

/-- Queue zero, all suffix Hall inequalities, and temporal matchability are
the same finite condition. -/
theorem finiteReflectedQueueOn_eq_zero_iff_forwardWindowMatching
    (arrivals service : ℕ → ℕ) {q m : ℕ} (hqm : q ≤ m) :
    finiteReflectedQueueOn arrivals service q m = 0 ↔
      FiniteForwardWindowMatching arrivals service q m := by
  rw [finiteForwardWindowMatching_iff_suffix_sum_le arrivals service hqm,
    finiteReflectedQueueOn_eq_zero_iff_all_suffix_nonpos arrivals service hqm]
  exact forall_congr' fun t => forall_congr' fun _ =>
    finiteSignedWindowBalance_nonpos_iff_sum_le arrivals service t m

end DkMath.Collatz
