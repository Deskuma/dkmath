/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue"

namespace DkMath.Collatz

/-!
# Anonymous scalar repayment queue

Recovery depth is an intrinsic source address.  Endpoint level is merely a
coordinate on anonymous unit-capacity slots.  The exact endpoint ledger gives
every complete claim weight one and every capacity slot weight one, so this
module deliberately forgets both coordinates and studies the causal scalar
queue.

Unused service is not banked.  At each block, new unit claims arrive, the
block's anonymous unit capacity serves the accumulated queue, and Nat
subtraction reflects a negative signed balance back to zero.
-/

/-! ## Block arrivals, service, and drift -/

/-- Number of complete unit claims born in canonical block `k`. -/
noncomputable def canonicalBlockClaimCount (n : OddNat) (k : ℕ) : ℕ :=
  (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card

/-- Number of anonymous unit-capacity slots born in canonical block `k`. -/
noncomputable def canonicalBlockCapacityCount (n : OddNat) (k : ℕ) : ℕ :=
  (canonicalEndpointCapacitySlots n k).card

/-- The endpoint accounting term is exactly scalar arrivals minus service. -/
theorem endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      (canonicalBlockClaimCount n k : ℤ) - canonicalBlockCapacityCount n k := by
  unfold endpointAccountingTerm canonicalBlockClaimCount canonicalBlockCapacityCount
  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
    n (paymentEndpointSeq n k)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
  rw [canonicalEndpointCapacitySlots_card]
  push_cast
  rfl

/-! ## Reflected outstanding queue -/

/-- Causal outstanding unit claims after canonical block `k` has served. -/
noncomputable def canonicalOutstandingClaimQueue (n : OddNat) : ℕ → ℕ
  | 0 => canonicalBlockClaimCount n 0 - canonicalBlockCapacityCount n 0
  | k + 1 => (canonicalOutstandingClaimQueue n k +
      canonicalBlockClaimCount n (k + 1)) - canonicalBlockCapacityCount n (k + 1)

/-- The queue's causal successor equation. -/
theorem canonicalOutstandingClaimQueue_succ
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueue n (k + 1) =
      (canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) -
        canonicalBlockCapacityCount n (k + 1) := rfl

/-- Service can never leave more than the old queue plus new arrivals. -/
theorem canonicalOutstandingClaimQueue_succ_le_arrivals
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueue n (k + 1) ≤
      canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1) := by
  rw [canonicalOutstandingClaimQueue_succ]
  exact Nat.sub_le _ _

/-- Enough current service empties the queue at the selected successor block. -/
theorem canonicalOutstandingClaimQueue_succ_eq_zero_of_le_capacity
    {n : OddNat} {k : ℕ}
    (h : canonicalOutstandingClaimQueue n k +
      canonicalBlockClaimCount n (k + 1) ≤ canonicalBlockCapacityCount n (k + 1)) :
    canonicalOutstandingClaimQueue n (k + 1) = 0 := by
  rw [canonicalOutstandingClaimQueue_succ, Nat.sub_eq_zero_of_le h]

/--
If service does not exceed available work, the successor equation is exact
addition/subtraction.
-/
theorem canonicalOutstandingClaimQueue_succ_add_capacity
    {n : OddNat} {k : ℕ}
    (h : canonicalBlockCapacityCount n (k + 1) ≤
      canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) :
    canonicalOutstandingClaimQueue n (k + 1) +
        canonicalBlockCapacityCount n (k + 1) =
      canonicalOutstandingClaimQueue n k +
        canonicalBlockClaimCount n (k + 1) := by
  rw [canonicalOutstandingClaimQueue_succ, Nat.sub_add_cancel h]

/-- Nat reflection is the nonnegative part of the corresponding signed step. -/
theorem natSub_eq_intToNat_add_sub (old arrivals service : ℕ) :
    (old + arrivals) - service =
      Int.toNat ((old : ℤ) + arrivals - service) := by
  omega

/-! ## Signed window drift -/

/-- Signed scalar drift over canonical blocks `q..m`. -/
noncomputable def canonicalWindowDriftInt
    (n : OddNat) (q m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k

/-- A singleton window has exactly its block drift. -/
theorem canonicalWindowDriftInt_self (n : OddNat) (m : ℕ) :
    canonicalWindowDriftInt n m m = endpointAccountingTerm n m := by
  simp [canonicalWindowDriftInt]

/-- Extending a nonempty-right window appends the new terminal block drift. -/
theorem canonicalWindowDriftInt_succ
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m + 1) :
    canonicalWindowDriftInt n q (m + 1) =
      (if q ≤ m then canonicalWindowDriftInt n q m else 0) +
        endpointAccountingTerm n (m + 1) := by
  by_cases hq : q ≤ m
  · rw [if_pos hq]
    unfold canonicalWindowDriftInt
    have hIcc : Finset.Icc q (m + 1) = insert (m + 1) (Finset.Icc q m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc]
    rw [Finset.sum_insert (by simp)]
    ring
  · have hqeq : q = m + 1 := by omega
    subst q
    simp [canonicalWindowDriftInt]

/-! ## Exact reflected-walk identity -/

/-- The initial queue is the nonnegative part of the initial signed drift. -/
theorem canonicalOutstandingClaimQueue_zero_eq_intToNat
    (n : OddNat) :
    canonicalOutstandingClaimQueue n 0 =
      Int.toNat (endpointAccountingTerm n 0) := by
  rw [canonicalOutstandingClaimQueue,
    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
  omega

/-- Every queue step is reflection of the old queue plus the new signed drift. -/
theorem canonicalOutstandingClaimQueue_succ_eq_intToNat
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueue n (k + 1) =
      Int.toNat ((canonicalOutstandingClaimQueue n k : ℤ) +
        endpointAccountingTerm n (k + 1)) := by
  rw [canonicalOutstandingClaimQueue_succ,
    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
  have harg :
      (canonicalOutstandingClaimQueue n k : ℤ) +
          canonicalBlockClaimCount n (k + 1) - canonicalBlockCapacityCount n (k + 1) =
        (canonicalOutstandingClaimQueue n k : ℤ) +
          ((canonicalBlockClaimCount n (k + 1) : ℤ) -
            canonicalBlockCapacityCount n (k + 1)) := by
    ring
  rw [← harg]
  exact natSub_eq_intToNat_add_sub _ _ _

/-- Every suffix's positive signed drift is bounded by the reflected queue. -/
theorem intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    Int.toNat (canonicalWindowDriftInt n q m) ≤
      canonicalOutstandingClaimQueue n m := by
  induction m with
  | zero =>
      have hq : q = 0 := by omega
      subst q
      rw [canonicalWindowDriftInt_self,
        canonicalOutstandingClaimQueue_zero_eq_intToNat]
  | succ m ih =>
      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
      by_cases hq : q ≤ m
      · rw [canonicalWindowDriftInt_succ n (by omega), if_pos hq]
        apply Int.toNat_le_toNat
        have hle := ih hq
        have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
        omega
      · have hqeq : q = m + 1 := by omega
        subst q
        rw [canonicalWindowDriftInt_self]
        apply Int.toNat_le_toNat
        omega

/-- A positive reflected queue is attained by one suffix's positive drift. -/
theorem outstandingClaimQueue_eq_zero_or_exists_windowDrift
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueue n m = 0 ∨
      (0 < canonicalOutstandingClaimQueue n m ∧
        ∃ q, q ≤ m ∧ canonicalOutstandingClaimQueue n m =
          Int.toNat (canonicalWindowDriftInt n q m)) := by
  induction m with
  | zero =>
      by_cases hzero : canonicalOutstandingClaimQueue n 0 = 0
      · exact Or.inl hzero
      · exact Or.inr ⟨Nat.pos_of_ne_zero hzero, 0, le_rfl, by
          rw [canonicalWindowDriftInt_self,
            canonicalOutstandingClaimQueue_zero_eq_intToNat]⟩
  | succ m ih =>
      by_cases hzero : canonicalOutstandingClaimQueue n (m + 1) = 0
      · exact Or.inl hzero
      · refine Or.inr ⟨Nat.pos_of_ne_zero hzero, ?_⟩
        rcases ih with hold | ⟨holdPos, q, hqm, holdWitness⟩
        · refine ⟨m + 1, le_rfl, ?_⟩
          rw [canonicalWindowDriftInt_self,
            canonicalOutstandingClaimQueue_succ_eq_intToNat, hold]
          simp
        · refine ⟨q, by omega, ?_⟩
          rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
          rw [canonicalWindowDriftInt_succ n (by omega), if_pos hqm]
          have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
            by_contra hneg
            have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 := by
              exact Int.toNat_of_nonpos (by omega)
            omega
          have hcast : (canonicalOutstandingClaimQueue n m : ℤ) =
              canonicalWindowDriftInt n q m := by
            rw [holdWitness, Int.ofNat_toNat, max_eq_left hnonneg]
          rw [hcast]

/-- Maximum positive suffix drift through block `m`, with zero included by `Finset.sup`. -/
noncomputable def canonicalReflectedWindowMaximum
    (n : OddNat) (m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup fun q =>
    Int.toNat (canonicalWindowDriftInt n q m)

/-- The causal queue is exactly the maximum positive signed suffix drift. -/
theorem canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueue n m = canonicalReflectedWindowMaximum n m := by
  apply le_antisymm
  · rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with hzero | hpos
    · rw [hzero]
      exact Nat.zero_le _
    · rcases hpos with ⟨_, q, hqm, hq⟩
      rw [hq]
      unfold canonicalReflectedWindowMaximum
      exact Finset.le_sup (f := fun q => Int.toNat (canonicalWindowDriftInt n q m))
        (Finset.mem_range.mpr (by omega))
  · unfold canonicalReflectedWindowMaximum
    apply Finset.sup_le
    intro q hq
    exact intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n
      (Nat.le_of_lt_succ (Finset.mem_range.mp hq))

/--
A pointwise queue ceiling is exactly a ceiling on every signed suffix drift
ending at the same block.  This is the useful bounded analogue of the
zero/repayment characterization below.
-/
theorem canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le
    (n : OddNat) (m C : ℕ) :
    canonicalOutstandingClaimQueue n m ≤ C ↔
      ∀ q, q ≤ m → canonicalWindowDriftInt n q m ≤ C := by
  constructor
  · intro hqueue q hqm
    have hdrift := intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n hqm
    have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
    omega
  · intro hall
    rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
      hzero | ⟨_, q, hqm, hq⟩
    · simp [hzero]
    · rw [hq]
      have hbound := hall q hqm
      omega

/-! ## Running-minimum form and repayment characterization -/

/-- Running minimum of zero and all canonical endpoint balances through `m`. -/
noncomputable def canonicalEndpointRunningBalanceMinimum
    (n : OddNat) : ℕ → ℤ
  | 0 => min 0 (canonicalEndpointBalanceInt n 0)
  | m + 1 => min (canonicalEndpointRunningBalanceMinimum n m)
      (canonicalEndpointBalanceInt n (m + 1))

/-- The running minimum is below the current endpoint balance. -/
theorem canonicalEndpointRunningBalanceMinimum_le_balance
    (n : OddNat) (m : ℕ) :
    canonicalEndpointRunningBalanceMinimum n m ≤ canonicalEndpointBalanceInt n m := by
  cases m with
  | zero => exact min_le_right _ _
  | succ m =>
      rw [canonicalEndpointRunningBalanceMinimum]
      exact min_le_right _ _

/-- The running minimum always includes the initial zero candidate. -/
theorem canonicalEndpointRunningBalanceMinimum_nonpos
    (n : OddNat) (m : ℕ) :
    canonicalEndpointRunningBalanceMinimum n m ≤ 0 := by
  induction m with
  | zero => exact min_le_left _ _
  | succ m ih =>
      rw [canonicalEndpointRunningBalanceMinimum]
      exact (min_le_left _ _).trans ih

/-- Exact running-minimum form of the reflected scalar queue. -/
theorem canonicalOutstandingClaimQueue_eq_balance_sub_runningMinimum
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueue n m = Int.toNat
      (canonicalEndpointBalanceInt n m -
        canonicalEndpointRunningBalanceMinimum n m) := by
  induction m with
  | zero =>
      rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
        canonicalEndpointRunningBalanceMinimum]
      rw [canonicalEndpointBalanceInt]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
      by_cases hterm : endpointAccountingTerm n 0 ≤ 0
      · rw [min_eq_right hterm]
        simp [Int.toNat_of_nonpos hterm]
      · rw [min_eq_left (by omega)]
        simp
  | succ m ih =>
      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
        canonicalEndpointRunningBalanceMinimum]
      have hbalance :
          canonicalEndpointBalanceInt n (m + 1) =
            canonicalEndpointBalanceInt n m + endpointAccountingTerm n (m + 1) := by
        unfold canonicalEndpointBalanceInt
        rw [Finset.sum_range_succ]
      rw [hbalance]
      have hminle := canonicalEndpointRunningBalanceMinimum_le_balance n m
      have hnonneg : 0 ≤ canonicalEndpointBalanceInt n m -
          canonicalEndpointRunningBalanceMinimum n m := sub_nonneg.mpr hminle
      have hcast :
          (Int.toNat (canonicalEndpointBalanceInt n m -
            canonicalEndpointRunningBalanceMinimum n m) : ℤ) =
              canonicalEndpointBalanceInt n m -
                canonicalEndpointRunningBalanceMinimum n m := by
        rw [Int.ofNat_toNat, max_eq_left hnonneg]
      rw [ih, hcast]
      by_cases hnew : canonicalEndpointBalanceInt n m +
          endpointAccountingTerm n (m + 1) ≤
            canonicalEndpointRunningBalanceMinimum n m
      · rw [min_eq_right hnew]
        have hnonpos : canonicalEndpointBalanceInt n m -
            canonicalEndpointRunningBalanceMinimum n m +
              endpointAccountingTerm n (m + 1) ≤ 0 := by
          linarith
        rw [Int.toNat_of_nonpos hnonpos]
        simp
      · rw [min_eq_left (by omega)]
        congr 1
        ring

/-- Queue zero means that every suffix ending at `m` has nonpositive drift. -/
theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueue n m = 0 ↔
      ∀ q, q ≤ m → canonicalWindowDriftInt n q m ≤ 0 := by
  constructor
  · intro hzero q hqm
    have hle := intToNat_canonicalWindowDriftInt_le_outstandingClaimQueue n hqm
    rw [hzero] at hle
    exact (Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle))
  · intro hall
    rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
      hzero | ⟨hpos, q, hqm, hq⟩
    · exact hzero
    · have hnonpos := hall q hqm
      have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
        Int.toNat_of_nonpos hnonpos
      omega

/-- Queue zero means every aggregate excursion ending at `m` is repaid. -/
theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_excursions_repaid
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueue n m = 0 ↔
      ∀ q, q ≤ m → CanonicalEndpointExcursionRepaidAt n q m := by
  rw [canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos]
  constructor
  · intro h q hqm
    exact (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqm).2 (h q hqm)
  · intro h q hqm
    exact (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqm).1 (h q hqm)

/-! ## Window-local causal queue -/

/--
Outstanding queue generated only by blocks `q..r`, initialized at zero before
block `q`.  The reflected suffix form is chosen as the public terminal value;
unlike aggregate drift, it remembers every possible release-time suffix.
-/
noncomputable def canonicalLocalOutstandingClaimQueue
    (n : OddNat) (q r : ℕ) : ℕ :=
  (Finset.Icc q r).sup fun t => Int.toNat (canonicalWindowDriftInt n t r)

/-- The local causal queue is zero exactly when every release-time suffix is nonpositive. -/
theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_all_suffixDrift_nonpos
    (n : OddNat) (q r : ℕ) :
    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
      ∀ t ∈ Finset.Icc q r, canonicalWindowDriftInt n t r ≤ 0 := by
  constructor
  · intro hzero t ht
    have hle : Int.toNat (canonicalWindowDriftInt n t r) ≤
        canonicalLocalOutstandingClaimQueue n q r := by
      unfold canonicalLocalOutstandingClaimQueue
      exact Finset.le_sup (f := fun t => Int.toNat (canonicalWindowDriftInt n t r)) ht
    rw [hzero] at hle
    exact Int.toNat_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
  · intro hall
    unfold canonicalLocalOutstandingClaimQueue
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro t ht
    rw [Int.toNat_of_nonpos (hall t ht)]

/-- Suffix drift inequalities are exactly suffix claim-versus-capacity inequalities. -/
theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_suffixClaims_le_capacity
    (n : OddNat) (q r : ℕ) :
    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
      ∀ t ∈ Finset.Icc q r,
        canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
  rw [canonicalLocalOutstandingClaimQueue_eq_zero_iff_all_suffixDrift_nonpos]
  constructor
  · intro h t ht
    have htr := (Finset.mem_Icc.mp ht).2
    have hrepaid : CanonicalEndpointExcursionRepaidAt n t r :=
      (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n htr).2 (by
        simpa [canonicalWindowDriftInt] using h t ht)
    exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n htr).1
      hrepaid
  · intro h t ht
    have htr := (Finset.mem_Icc.mp ht).2
    have hrepaid : CanonicalEndpointExcursionRepaidAt n t r :=
      (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n htr).2
        (h t ht)
    simpa [canonicalWindowDriftInt] using
      (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n htr).1 hrepaid

/-! ## Temporal matching and suffix Hall conditions -/

/-- A causal forward matching forces every release-time suffix Hall inequality. -/
theorem CanonicalEndpointForwardWindowMatching.to_suffixClaims_le_capacity
    {n : OddNat} {q r : ℕ}
    (h : CanonicalEndpointForwardWindowMatching n q r) :
    ∀ t ∈ Finset.Icc q r,
      canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
  classical
  rcases h with ⟨hqr, pay, hpayInjective, hpayForward⟩
  intro t ht
  have hqt := (Finset.mem_Icc.mp ht).1
  have htr := (Finset.mem_Icc.mp ht).2
  let includeClaim : CanonicalEndpointClaimWindowCarrier n t r →
      CanonicalEndpointClaimWindowCarrier n q r := fun claim =>
    ⟨⟨claim.1.val, Finset.mem_Icc.mpr
      ⟨hqt.trans (Finset.mem_Icc.mp claim.1.property).1,
        (Finset.mem_Icc.mp claim.1.property).2⟩⟩,
      claim.2⟩
  have includeClaim_injective : Function.Injective includeClaim := by
    intro a b hab
    rcases a with ⟨ak, ai⟩
    rcases b with ⟨bk, bi⟩
    apply Sigma.ext_iff.mpr
    constructor
    · exact Subtype.ext (congrArg (fun claim => claim.1.val) hab)
    · exact (Sigma.ext_iff.mp hab).2
  let suffixPay : CanonicalEndpointClaimWindowCarrier n t r →
      CanonicalEndpointCapacityWindowCarrier n t r := fun claim =>
    ⟨⟨(pay (includeClaim claim)).1.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp claim.1.property).1.trans
          (hpayForward (includeClaim claim)),
        (Finset.mem_Icc.mp (pay (includeClaim claim)).1.property).2⟩⟩,
      (pay (includeClaim claim)).2⟩
  have suffixPay_injective : Function.Injective suffixPay := by
    intro a b hab
    apply includeClaim_injective
    apply hpayInjective
    rcases a with ⟨ak, ai⟩
    rcases b with ⟨bk, bi⟩
    apply Sigma.ext_iff.mpr
    constructor
    · exact Subtype.ext (congrArg (fun slot => slot.1.val) hab)
    · exact (Sigma.ext_iff.mp hab).2
  letI : Finite (CanonicalEndpointCapacityWindowCarrier n t r) := by
    unfold CanonicalEndpointCapacityWindowCarrier
    infer_instance
  have hcard := Nat.card_le_card_of_injective suffixPay suffixPay_injective
  rw [natCard_canonicalEndpointClaimWindowCarrier,
    natCard_canonicalEndpointCapacityWindowCarrier] at hcard
  exact hcard

/-- Nested suffix Hall inequalities construct an anonymous causal forward matching. -/
theorem canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity
    {n : OddNat} {q r : ℕ} (hqr : q ≤ r)
    (hall : ∀ t ∈ Finset.Icc q r,
      canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r) :
    CanonicalEndpointForwardWindowMatching n q r := by
  classical
  let Claim := CanonicalEndpointClaimWindowCarrier n q r
  let Capacity := CanonicalEndpointCapacityWindowCarrier n q r
  letI : Finite Claim := by
    dsimp [Claim]
    unfold CanonicalEndpointClaimWindowCarrier
    infer_instance
  letI : Finite Capacity := by
    dsimp [Capacity]
    unfold CanonicalEndpointCapacityWindowCarrier
    infer_instance
  letI : Fintype Claim := Fintype.ofFinite Claim
  letI : Fintype Capacity := Fintype.ofFinite Capacity
  let eligible : Claim → Capacity → Prop := fun claim slot => claim.1.val ≤ slot.1.val
  have hallSubsets : ∀ A : Finset Claim,
      A.card ≤ ({slot : Capacity | ∃ claim ∈ A, eligible claim slot} : Finset Capacity).card := by
    intro A
    by_cases hA : A.Nonempty
    · let blocks : Finset ℕ := A.image fun claim => claim.1.val
      have hblocks : blocks.Nonempty := hA.image _
      let t := blocks.min' hblocks
      have htBlocks : t ∈ blocks := Finset.min'_mem blocks hblocks
      rcases Finset.mem_image.mp htBlocks with ⟨minClaim, hminClaimA, hminClaimBlock⟩
      have htIcc : t ∈ Finset.Icc q r := by
        rw [← hminClaimBlock]
        exact minClaim.1.property
      have ht_le_claim : ∀ claim ∈ A, t ≤ claim.1.val := by
        intro claim hclaim
        exact Finset.min'_le blocks _ (Finset.mem_image.mpr ⟨claim, hclaim, rfl⟩)
      let claimsFromT : ↥A → CanonicalEndpointClaimWindowCarrier n t r := fun claim =>
        ⟨⟨claim.val.1.val, Finset.mem_Icc.mpr
          ⟨ht_le_claim claim.val claim.property,
            (Finset.mem_Icc.mp claim.val.1.property).2⟩⟩,
          claim.val.2⟩
      have claimsFromT_injective : Function.Injective claimsFromT := by
        intro a b hab
        apply Subtype.ext
        rcases a with ⟨a, ha⟩
        rcases b with ⟨b, hb⟩
        apply Sigma.ext_iff.mpr
        constructor
        · exact Subtype.ext (congrArg (fun claim => claim.1.val) hab)
        · exact (Sigma.ext_iff.mp hab).2
      have hAClaims : A.card ≤ canonicalEndpointWindowClaims n t r := by
        letI : Finite (CanonicalEndpointClaimWindowCarrier n t r) := by
          unfold CanonicalEndpointClaimWindowCarrier
          infer_instance
        letI : Fintype (CanonicalEndpointClaimWindowCarrier n t r) :=
          Fintype.ofFinite _
        have hcard := Fintype.card_le_of_injective claimsFromT claimsFromT_injective
        rw [← natCard_canonicalEndpointClaimWindowCarrier n t r]
        simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
      let capacityToEligible : CanonicalEndpointCapacityWindowCarrier n t r →
          {slot : Capacity // ∃ claim ∈ A, eligible claim slot} := fun slot =>
        ⟨⟨⟨slot.1.val, Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp htIcc).1.trans
                (Finset.mem_Icc.mp slot.1.property).1,
              (Finset.mem_Icc.mp slot.1.property).2⟩⟩,
            slot.2⟩,
          ⟨minClaim, hminClaimA, by
            change minClaim.1.val ≤ slot.1.val
            rw [hminClaimBlock]
            exact (Finset.mem_Icc.mp slot.1.property).1⟩⟩
      have capacityToEligible_injective : Function.Injective capacityToEligible := by
        intro a b hab
        rcases a with ⟨ak, ai⟩
        rcases b with ⟨bk, bi⟩
        apply Sigma.ext_iff.mpr
        constructor
        · exact Subtype.ext (congrArg (fun slot => slot.val.1.val) hab)
        · have hsigma :
              (capacityToEligible ⟨ak, ai⟩).val =
                (capacityToEligible ⟨bk, bi⟩).val := congrArg Subtype.val hab
          exact (Sigma.ext_iff.mp hsigma).2
      have hCapacityEligible : canonicalEndpointWindowCapacity n t r ≤
          ({slot : Capacity | ∃ claim ∈ A, eligible claim slot} : Finset Capacity).card := by
        letI : Finite (CanonicalEndpointCapacityWindowCarrier n t r) := by
          unfold CanonicalEndpointCapacityWindowCarrier
          infer_instance
        letI : Fintype (CanonicalEndpointCapacityWindowCarrier n t r) :=
          Fintype.ofFinite _
        have hcard := Fintype.card_le_of_injective capacityToEligible
          capacityToEligible_injective
        rw [← natCard_canonicalEndpointCapacityWindowCarrier n t r]
        rw [Nat.card_eq_fintype_card]
        rw [Fintype.card_subtype] at hcard
        exact hcard
      exact hAClaims.trans ((hall t htIcc).trans hCapacityEligible)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp
  have hmatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective eligible).1 hallSubsets
  rcases hmatching with ⟨pay, hpay, heligible⟩
  exact ⟨hqr, pay, hpay, heligible⟩

/-- Anonymous temporal Hall theorem for canonical block windows. -/
theorem canonicalEndpointForwardWindowMatching_iff_suffixClaims_le_capacity
    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
    CanonicalEndpointForwardWindowMatching n q r ↔
      ∀ t ∈ Finset.Icc q r,
        canonicalEndpointWindowClaims n t r ≤ canonicalEndpointWindowCapacity n t r := by
  constructor
  · exact CanonicalEndpointForwardWindowMatching.to_suffixClaims_le_capacity
  · exact canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity hqr

/-- Local causal queue zero is exactly anonymous forward matchability. -/
theorem canonicalLocalOutstandingClaimQueue_eq_zero_iff_forwardWindowMatching
    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
    canonicalLocalOutstandingClaimQueue n q r = 0 ↔
      CanonicalEndpointForwardWindowMatching n q r := by
  rw [canonicalEndpointForwardWindowMatching_iff_suffixClaims_le_capacity n hqr]
  exact canonicalLocalOutstandingClaimQueue_eq_zero_iff_suffixClaims_le_capacity n q r

/-! ## Exact scalar regressions -/

/-- The first seven block leaves one anonymous unit claim outstanding. -/
theorem canonicalOutstandingClaimQueue_seven_zero :
    canonicalOutstandingClaimQueue sevenDepthRegressionRoot 0 = 1 := by
  rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
    endpointAccountingTerm_sevenDepthRegressionRoot_zero]
  decide

/-- The second seven block repays the first scalar queue completely. -/
theorem canonicalOutstandingClaimQueue_seven_one :
    canonicalOutstandingClaimQueue sevenDepthRegressionRoot 1 = 0 := by
  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
    canonicalOutstandingClaimQueue_seven_zero,
    endpointAccountingTerm_sevenDepthRegressionRoot_one]
  decide

/-- The first two seven blocks admit an actual anonymous causal forward matching. -/
theorem canonicalEndpointForwardWindowMatching_seven_zero_one :
    CanonicalEndpointForwardWindowMatching sevenDepthRegressionRoot 0 1 := by
  apply canonicalEndpointForwardWindowMatching_of_suffixClaims_le_capacity (by omega)
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨ht0, ht1⟩
  interval_cases t
  · exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
      sevenDepthRegressionRoot (by omega)).1 (by
        apply (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
          sevenDepthRegressionRoot (by omega)).2
        rw [show (∑ k ∈ Finset.Icc 0 1,
            endpointAccountingTerm sevenDepthRegressionRoot k) =
              endpointAccountingTerm sevenDepthRegressionRoot 0 +
                endpointAccountingTerm sevenDepthRegressionRoot 1 by
          rw [show Finset.Icc 0 1 = {0, 1} by decide]
          simp]
        rw [endpointAccountingTerm_sevenDepthRegressionRoot_zero,
          endpointAccountingTerm_sevenDepthRegressionRoot_one]
        norm_num)
  · exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
      sevenDepthRegressionRoot (by omega)).1 (by
        apply (canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
          sevenDepthRegressionRoot (by omega)).2
        rw [show (∑ k ∈ Finset.Icc 1 1,
            endpointAccountingTerm sevenDepthRegressionRoot k) =
              endpointAccountingTerm sevenDepthRegressionRoot 1 by norm_num]
        rw [endpointAccountingTerm_sevenDepthRegressionRoot_one]
        norm_num)

/-! ### The scalar repayment regression from 511 -/

/-- Public root used by the exact scalar-queue regression from 511. -/
def scalarQueue511Root : OddNat := mkOddNat 511 (by decide)

private lemma scalarQueue511_v2_1534 : v2 1534 = 1 := by
  rw [show 1534 = 2 * 767 by norm_num, v2_two_mul 767 (by norm_num)]
  rw [v2_odd 767 (by decide)]

private lemma scalarQueue511_v2_2302 : v2 2302 = 1 := by
  rw [show 2302 = 2 * 1151 by norm_num, v2_two_mul 1151 (by norm_num)]
  rw [v2_odd 1151 (by decide)]

private lemma scalarQueue511_v2_3454 : v2 3454 = 1 := by
  rw [show 3454 = 2 * 1727 by norm_num, v2_two_mul 1727 (by norm_num)]
  rw [v2_odd 1727 (by decide)]

private lemma scalarQueue511_v2_5182 : v2 5182 = 1 := by
  rw [show 5182 = 2 * 2591 by norm_num, v2_two_mul 2591 (by norm_num)]
  rw [v2_odd 2591 (by decide)]

private lemma scalarQueue511_v2_7774 : v2 7774 = 1 := by
  rw [show 7774 = 2 * 3887 by norm_num, v2_two_mul 3887 (by norm_num)]
  rw [v2_odd 3887 (by decide)]

private lemma scalarQueue511_v2_11662 : v2 11662 = 1 := by
  rw [show 11662 = 2 * 5831 by norm_num, v2_two_mul 5831 (by norm_num)]
  rw [v2_odd 5831 (by decide)]

private lemma scalarQueue511_v2_17494 : v2 17494 = 1 := by
  rw [show 17494 = 2 * 8747 by norm_num, v2_two_mul 8747 (by norm_num)]
  rw [v2_odd 8747 (by decide)]

private lemma scalarQueue511_v2_26242 : v2 26242 = 1 := by
  rw [show 26242 = 2 * 13121 by norm_num, v2_two_mul 13121 (by norm_num)]
  rw [v2_odd 13121 (by decide)]

private lemma scalarQueue511_v2_39364 : v2 39364 = 2 := by
  rw [show 39364 = 2 * (2 * 9841) by norm_num]
  rw [v2_two_mul (2 * 9841) (by norm_num), v2_two_mul 9841 (by norm_num)]
  rw [v2_odd 9841 (by decide)]

private lemma scalarQueue511_v2_29524 : v2 29524 = 2 := by
  rw [show 29524 = 2 * (2 * 7381) by norm_num]
  rw [v2_two_mul (2 * 7381) (by norm_num), v2_two_mul 7381 (by norm_num)]
  rw [v2_odd 7381 (by decide)]

private lemma scalarQueue511_v2_22144 : v2 22144 = 7 := by
  rw [show 22144 = 2 * (2 * (2 * (2 * (2 * (2 * (2 * 173)))))) by norm_num]
  repeat' rw [v2_two_mul _ (by norm_num)]
  rw [v2_odd 173 (by decide)]

private lemma scalarQueue511_v2_512 : v2 512 = 9 := by
  simpa [pow2] using v2_pow2 9

private lemma scalarQueue511_v2_9842 : v2 9842 = 1 := by
  rw [show 9842 = 2 * 4921 by norm_num, v2_two_mul 4921 (by norm_num)]
  rw [v2_odd 4921 (by decide)]

private lemma scalarQueue511_v2_7382 : v2 7382 = 1 := by
  rw [show 7382 = 2 * 3691 by norm_num, v2_two_mul 3691 (by norm_num)]
  rw [v2_odd 3691 (by decide)]

private theorem scalarQueue511_endpoint_zero :
    paymentEndpointSeq scalarQueue511Root 0 = 8 := by
  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
    ResidualAllOnesDepth, oddOrbitLabel, iterateT, scalarQueue511Root, mkOddNat,
    scalarQueue511_v2_512]

private theorem scalarQueue511_endpoint_one :
    paymentEndpointSeq scalarQueue511Root 1 = 9 := by
  rw [show paymentEndpointSeq scalarQueue511Root 1 =
    orbitPaymentTarget scalarQueue511Root
      (paymentEndpointSeq scalarQueue511Root 0 + 1) by rfl]
  rw [scalarQueue511_endpoint_zero]
  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth,
    oddOrbitLabel, iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
    scalarQueue511_v2_39364, scalarQueue511_v2_9842]

private theorem scalarQueue511_endpoint_two :
    paymentEndpointSeq scalarQueue511Root 2 = 10 := by
  rw [show paymentEndpointSeq scalarQueue511Root 2 =
    orbitPaymentTarget scalarQueue511Root
      (paymentEndpointSeq scalarQueue511Root 1 + 1) by rfl]
  rw [scalarQueue511_endpoint_one]
  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth,
    oddOrbitLabel, iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
    scalarQueue511_v2_39364, scalarQueue511_v2_29524,
    scalarQueue511_v2_7382]

private theorem endpointAccountingTerm_scalarQueue511_zero :
    endpointAccountingTerm scalarQueue511Root 0 = 5 := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
    (paymentEndpointSeq scalarQueue511Root 0)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 0)]
  rw [universalPaymentBlockStart_paymentEndpointSeq_zero,
    scalarQueue511_endpoint_zero]
  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
    scalarQueue511_v2_39364, bitWidth]

private theorem endpointAccountingTerm_scalarQueue511_one :
    endpointAccountingTerm scalarQueue511Root 1 = -1 := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
    (paymentEndpointSeq scalarQueue511Root 1)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 1)]
  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
    scalarQueue511_endpoint_zero, scalarQueue511_endpoint_one]
  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
    scalarQueue511_v2_39364, scalarQueue511_v2_29524, bitWidth]

private theorem endpointAccountingTerm_scalarQueue511_two :
    endpointAccountingTerm scalarQueue511Root 2 = -5 := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub scalarQueue511Root
    (paymentEndpointSeq scalarQueue511Root 2)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq scalarQueue511Root 2)]
  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
    scalarQueue511_endpoint_one, scalarQueue511_endpoint_two]
  norm_num [iterateT, T, scalarQueue511Root, mkOddNat, threeNPlusOne, pow2,
    scalarQueue511_v2_1534, scalarQueue511_v2_2302,
    scalarQueue511_v2_3454, scalarQueue511_v2_5182,
    scalarQueue511_v2_7774, scalarQueue511_v2_11662,
    scalarQueue511_v2_17494, scalarQueue511_v2_26242,
    scalarQueue511_v2_39364, scalarQueue511_v2_29524,
    scalarQueue511_v2_22144, bitWidth]

/-- The first 511 block leaves five anonymous claims outstanding. -/
theorem canonicalOutstandingClaimQueue_511_zero :
    canonicalOutstandingClaimQueue scalarQueue511Root 0 = 5 := by
  rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
    endpointAccountingTerm_scalarQueue511_zero]
  decide

/-- The second 511 block repays one of the five anonymous claims. -/
theorem canonicalOutstandingClaimQueue_511_one :
    canonicalOutstandingClaimQueue scalarQueue511Root 1 = 4 := by
  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
    canonicalOutstandingClaimQueue_511_zero,
    endpointAccountingTerm_scalarQueue511_one]
  decide

/-- The third 511 block repays the remaining scalar debt completely. -/
theorem canonicalOutstandingClaimQueue_511_two :
    canonicalOutstandingClaimQueue scalarQueue511Root 2 = 0 := by
  rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
    canonicalOutstandingClaimQueue_511_one,
    endpointAccountingTerm_scalarQueue511_two]
  decide

/-! ## Queue to endpoint balance -/

/-- The signed endpoint balance never exceeds the nonnegative outstanding queue. -/
theorem canonicalEndpointBalanceInt_le_outstandingClaimQueue
    (n : OddNat) (m : ℕ) :
    canonicalEndpointBalanceInt n m ≤ canonicalOutstandingClaimQueue n m := by
  induction m with
  | zero =>
      rw [canonicalEndpointBalanceInt, canonicalOutstandingClaimQueue]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
      rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
      omega
  | succ m ih =>
      rw [canonicalEndpointBalanceInt]
      rw [Finset.sum_range_succ, canonicalOutstandingClaimQueue_succ]
      rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
      rw [canonicalEndpointBalanceInt] at ih
      omega

/-- Uniform boundedness of the anonymous scalar queue. -/
def CanonicalOutstandingClaimQueueUniformUpperBound
    (n : OddNat) (C : ℕ) : Prop :=
  ∀ m, canonicalOutstandingClaimQueue n m ≤ C

/--
Uniform queue boundedness is precisely uniform control of every finite suffix
drift.  Reflection and Hall theory therefore reduce the remaining global
problem to this scalar signed-window estimate; they do not prove the estimate.
-/
theorem canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le
    (n : OddNat) (C : ℕ) :
    CanonicalOutstandingClaimQueueUniformUpperBound n C ↔
      ∀ m q, q ≤ m → canonicalWindowDriftInt n q m ≤ C := by
  constructor
  · intro h m
    exact (canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le n m C).1 (h m)
  · intro h m
    exact (canonicalOutstandingClaimQueue_le_iff_all_windowDrift_le n m C).2 (h m)

/-- A scalar queue ceiling supplies the existing canonical endpoint balance ceiling. -/
theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_balanceUniformUpperBound
    {n : OddNat} {C : ℕ}
    (h : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    CanonicalEndpointBalanceUniformUpperBound n C := by
  intro m
  exact (canonicalEndpointBalanceInt_le_outstandingClaimQueue n m).trans
    (Int.ofNat_le.mpr (h m))

/-- A scalar queue ceiling yields the corresponding canonical endpoint bit-width ceiling. -/
theorem bitWidth_paymentEndpointSeq_le_of_outstandingClaimQueueUniformUpperBound
    {n : OddNat} {C : ℕ}
    (h : CanonicalOutstandingClaimQueueUniformUpperBound n C) (m : ℕ) :
    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 + C :=
  bitWidth_paymentEndpointSeq_le_of_balanceUniformUpperBound
    h.to_balanceUniformUpperBound m

/-!
## Structural frontier after the scalar audit

The cp-316 executable audit inspected every odd root through `16383`.  In that
finite sample, all `8192` roots reached a canonical endpoint whose state is one
with queue zero.  The largest observed queue was eight and the longest observed
positive excursion lasted twenty canonical blocks.  These are regression data,
not universal constants.

The exact reflection theorem above explains the remaining obstruction.  A
uniform queue bound is equivalent to a uniform upper bound on every positive
suffix of `endpointAccountingTerm`.  Existing block length, claim-depth
histogram, endpoint height, pressure-contribution, and PatternLedger data
describe individual transitions, but no current theorem prevents an
arbitrarily long sequence of blocks from accumulating positive suffix drift.
Likewise, the temporal Hall theorem characterizes zero queue; it does not bound
a nonzero queue.

Consequently the next mathematical input must be one of the following, rather
than another depth-to-level eligibility rule:

* a uniform signed-suffix estimate;
* a uniform repayment-lag theorem;
* exclusion of a pumpable positive-queue transition cycle; or
* a finite-state obstruction that forces discharge.

Until one of those statements is proved, promoting the observed constants
`8` or `20` to a theorem would be unjustified.
-/

end DkMath.Collatz
