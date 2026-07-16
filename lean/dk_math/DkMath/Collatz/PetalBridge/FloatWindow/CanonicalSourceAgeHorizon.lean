/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon"

namespace DkMath.Collatz

/-!
# Canonical source-age horizon arithmetic

This module studies the signed frontier while the source-age horizon moves.
It keeps the finite-certificate and arithmetic questions separate: no signature
or potential below is manufactured from the deficit or its prefix sums.
-/

/-! ## Concrete saturation witness -/

/-- The smallest odd root found by the bounded discovery audit whose initial
canonical block is saturated.  The theorem below rechecks the witness in Lean;
the numerical search is not part of the proof. -/
def fiftyNineSaturatedOdd : OddNat := ⟨59, by norm_num⟩

private lemma fiftyNine_v2_60 : v2 60 = 2 := by
  have h30 := (DkMath.ABC.padic_val_two_of_even 30).2 (by decide)
  have h15 := (DkMath.ABC.padic_val_two_of_even 15).2 (by decide)
  have hv15 : v2 15 = 0 := v2_odd 15 (by decide)
  have hv30 : v2 30 = 1 := by simpa [v2, hv15] using h15
  simpa [v2, hv30] using h30

private lemma fiftyNine_v2_178 : v2 178 = 1 := by
  have h89 := (DkMath.ABC.padic_val_two_of_even 89).2 (by decide)
  simpa [v2, v2_odd 89 (by decide)] using h89

private lemma fiftyNine_v2_134 : v2 134 = 1 := by
  have h67 := (DkMath.ABC.padic_val_two_of_even 67).2 (by decide)
  simpa [v2, v2_odd 67 (by decide)] using h67

private theorem fiftyNine_endpoint_zero :
    paymentEndpointSeq fiftyNineSaturatedOdd 0 = 1 := by
  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
    ResidualAllOnesDepth, oddOrbitLabel, iterateT,
    fiftyNineSaturatedOdd, mkOddNat, fiftyNine_v2_60]

private theorem fiftyNine_paymentBlockLength_zero :
    canonicalPaymentBlockLength fiftyNineSaturatedOdd 0 = 2 := by
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
    universalPaymentBlockStart_paymentEndpointSeq_zero,
    fiftyNine_endpoint_zero]

@[simp] theorem canonicalBlockLength_fiftyNine_zero :
    canonicalBlockLength fiftyNineSaturatedOdd 0 = 2 :=
  fiftyNine_paymentBlockLength_zero

private theorem canonicalBlockStartState_fiftyNine_zero :
    canonicalBlockStartState fiftyNineSaturatedOdd 0 = 59 := by
  unfold canonicalBlockStartState canonicalBlockStartTime
    canonicalEndpointBlockStart
  rfl

private theorem canonicalBlockOddCore_fiftyNine_zero :
    canonicalBlockOddCore fiftyNineSaturatedOdd 0 = 15 := by
  rw [canonicalBlockOddCore, canonicalBlockStartState_fiftyNine_zero,
    canonicalBlockLength_fiftyNine_zero]
  norm_num

@[simp] theorem canonicalBlockTerminalValuation_fiftyNine_zero :
    canonicalBlockTerminalValuation fiftyNineSaturatedOdd 0 = 1 := by
  rw [canonicalBlockTerminalValuation, canonicalBlockTerminalCarrier,
    canonicalBlockLength_fiftyNine_zero,
    canonicalBlockOddCore_fiftyNine_zero]
  norm_num [fiftyNine_v2_134]

private theorem fiftyNine_carry_zero :
    CarryTwoDebtAt fiftyNineSaturatedOdd 0 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, fiftyNineSaturatedOdd, mkOddNat]

private theorem fiftyNine_carry_one :
    CarryTwoDebtAt fiftyNineSaturatedOdd 1 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, fiftyNineSaturatedOdd, mkOddNat, threeNPlusOne,
    pow2, fiftyNine_v2_178]

theorem canonicalPaymentClaimDepths_fiftyNine_zero :
    canonicalPaymentClaimDepths fiftyNineSaturatedOdd 0 = {1, 2} := by
  classical
  ext d
  rw [mem_canonicalPaymentClaimDepths_iff,
    fiftyNine_paymentBlockLength_zero]
  unfold canonicalPaymentSourceAtDepth
  rw [fiftyNine_endpoint_zero]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd1, hd2, hcarry⟩
    interval_cases d <;> simp_all
  · rintro (rfl | rfl) <;>
      simp [fiftyNine_carry_zero, fiftyNine_carry_one]

@[simp] theorem canonicalBlockClaimCount_fiftyNine_zero :
    canonicalBlockClaimCount fiftyNineSaturatedOdd 0 = 2 := by
  rw [canonicalBlockClaimCount_eq_claimDepths_card,
    canonicalPaymentClaimDepths_fiftyNine_zero]
  decide

/-- A fully checked saturated canonical block exists. -/
theorem canonicalSaturatedBorderBlock_fiftyNine_zero :
    CanonicalSaturatedBorderBlock fiftyNineSaturatedOdd 0 := by
  rw [canonicalSaturatedBorderBlock_iff_length_and_claims]
  simp

theorem exists_canonicalSaturatedBorderBlock :
    ∃ n m, CanonicalSaturatedBorderBlock n m :=
  ⟨fiftyNineSaturatedOdd, 0, canonicalSaturatedBorderBlock_fiftyNine_zero⟩

/-- Horizon-zero pointwise nonpositivity is formally false, not merely
conditionally obstructed. -/
theorem not_forall_sourceAgeFrontierIncrement_zero_nonpos :
    ¬ ∀ n m, canonicalSourceAgeFrontierIncrement n 0 m ≤ 0 := by
  intro h
  have hpos :=
    canonicalSaturatedBorderBlock_fiftyNine_zero.sourceAgeFrontierIncrement_zero_eq_one
  have hnonpos := h fiftyNineSaturatedOdd 0
  omega

/-! ## Horizon-zero queue compatibility -/

/-- At horizon zero, source-age arrivals are exactly current block demand. -/
theorem canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed
    (n : OddNat) (m : ℕ) :
    canonicalSourceAgeFrontierIncrement n 0 m =
      (canonicalQueueDemand n m : ℤ) - canonicalQueueConsumed n m := by
  unfold canonicalSourceAgeFrontierIncrement
  rw [canonicalSourceAgeHorizonCrossingClaims_zero_horizon,
    card_canonicalBlockClaimSourceCarrier]

/-- The horizon-zero frontier increment is exactly the signed scalar-queue
change across one canonical block. -/
theorem canonicalSourceAgeFrontierIncrement_zero_eq_queueBeforeBlock_diff
    (n : OddNat) (m : ℕ) :
    canonicalSourceAgeFrontierIncrement n 0 m =
      (canonicalOutstandingClaimQueueBeforeBlock n (m + 1) : ℤ) -
        canonicalOutstandingClaimQueueBeforeBlock n m := by
  rw [canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed]
  simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
  have hbalance := canonicalOutstandingClaimQueue_add_consumed n m
  omega

/-- A saturated block raises the horizon-zero queue by exactly one. -/
theorem CanonicalSaturatedBorderBlock.queueBeforeBlock_succ_eq_add_one
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalOutstandingClaimQueueBeforeBlock n (m + 1) =
      canonicalOutstandingClaimQueueBeforeBlock n m + 1 := by
  have hflow := canonicalSourceAgeFrontierIncrement_zero_eq_queueBeforeBlock_diff n m
  rw [h.sourceAgeFrontierIncrement_zero_eq_one] at hflow
  omega

/-! ## Genuinely finite-facing potential certificate -/

/-- A finite signature certificate whose potential is globally maximized at
the initial canonical signature.  Unlike the compatibility wrapper in the
previous module, this structure contains no all-time prefix field: with a
`Fintype Signature`, `potential_le_initial` is a finite verification problem.

The signature, transition relation, and potential remain externally supplied.
Defining them from the source-age deficit would still be circular. -/
structure CanonicalFiniteSourceAgeFrontierPotentialCertificate
    (n : OddNat) (H : ℕ) (Signature : Type*) [Fintype Signature] where
  certificate :
    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature
  step_succ : ∀ m, certificate.Step m (m + 1)
  actualWeight_succ : ∀ m,
    certificate.actualWeight m (m + 1) =
      canonicalSourceAgeFrontierIncrement n H m
  potential_le_initial : ∀ s : Signature,
    certificate.potential s ≤
      certificate.potential (certificate.signature 0)

namespace CanonicalFiniteSourceAgeFrontierPotentialCertificate

variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]

theorem prefixPotentialChange_nonpos
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature)
    (m : ℕ) :
    F.certificate.potential (F.certificate.signature m) -
      F.certificate.potential (F.certificate.signature 0) ≤ 0 := by
  have := F.potential_le_initial (F.certificate.signature m)
  omega

/-- Forget the finite initial-maximum field into the cp-336 compatibility
surface. -/
def toPotentialCertificate
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
    CanonicalSourceAgeFrontierPotentialCertificate n H Signature where
  certificate := F.certificate
  step_succ := F.step_succ
  actualWeight_succ := F.actualWeight_succ
  prefixPotentialChange_nonpos := F.prefixPotentialChange_nonpos

theorem to_sourceAgeAtMost
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H :=
  F.toPotentialCertificate.to_sourceAgeAtMost

theorem to_queue_and_endpointWidth_bounds
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature) :
    CanonicalOutstandingClaimQueueUniformUpperBound n H ∧
      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
  F.toPotentialCertificate.to_queue_and_endpointWidth_bounds

end CanonicalFiniteSourceAgeFrontierPotentialCertificate

/-! ## Carry-two boundary indicator -/

/-- Natural indicator of a carry-two source event. -/
noncomputable def canonicalCarryTwoIndicator (n : OddNat) (i : ℕ) : ℕ :=
  by
    classical
    exact if CarryTwoDebtAt n i then 1 else 0

@[simp] theorem canonicalCarryTwoIndicator_eq_one_iff
    (n : OddNat) (i : ℕ) :
    canonicalCarryTwoIndicator n i = 1 ↔ CarryTwoDebtAt n i := by
  classical
  simp [canonicalCarryTwoIndicator]

@[simp] theorem canonicalCarryTwoIndicator_eq_zero_iff
    (n : OddNat) (i : ℕ) :
    canonicalCarryTwoIndicator n i = 0 ↔ ¬ CarryTwoDebtAt n i := by
  classical
  simp [canonicalCarryTwoIndicator]

theorem card_carryTwoPositions_singleton
    (n : OddNat) (i : ℕ) :
    (carryTwoPositions n {i}).card = canonicalCarryTwoIndicator n i := by
  classical
  by_cases hi : CarryTwoDebtAt n i
  · have hcarrier : carryTwoPositions n {i} = {i} := by
      ext j
      simp only [mem_carryTwoPositions_iff, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro hji
        subst j
        exact ⟨rfl, hi⟩
    rw [hcarrier]
    simp [canonicalCarryTwoIndicator, hi]
  · have hcarrier : carryTwoPositions n {i} = ∅ := by
      ext j
      simp only [mem_carryTwoPositions_iff, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      rintro ⟨hji, hjCarry⟩
      exact hi (hji ▸ hjCarry)
    rw [hcarrier]
    simp [canonicalCarryTwoIndicator, hi]

theorem int_card_carryTwoPositions_singleton
    (n : OddNat) (i : ℕ) :
    ((carryTwoPositions n {i}).card : ℤ) = canonicalCarryTwoIndicator n i := by
  rw [card_carryTwoPositions_singleton]

/-! ## Exact old-carrier horizon shift -/

/-- In the mature regime, raising the source-age horizon erases exactly the
new cutoff boundary from the old-source carrier.  Whether this changes the
carrier is decided by the carry-two predicate at that boundary. -/
theorem canonicalOldSourceClaimCarrier_succ_horizon_of_lt_start
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    canonicalOldSourceClaimCarrier n (H + 1) m =
      (canonicalOldSourceClaimCarrier n H m).erase
        (canonicalBlockStartTime n m - H - 1) := by
  classical
  ext i
  simp only [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff,
    Finset.mem_Ico, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hi0, hiTop⟩, hiCarry⟩
    refine ⟨?_, ⟨⟨hi0, by omega⟩, hiCarry⟩⟩
    omega
  · rintro ⟨hiNe, ⟨⟨hi0, hiTop⟩, hiCarry⟩⟩
    exact ⟨⟨hi0, by omega⟩, hiCarry⟩

/-- Exact signed deficit decrement when the mature horizon advances once. -/
theorem canonicalSourceAgeDeficit_succ_horizon_of_lt_start
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    canonicalSourceAgeDeficit n (H + 1) m =
      canonicalSourceAgeDeficit n H m -
        canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n m - H - 1) := by
  classical
  let i := canonicalBlockStartTime n m - H - 1
  have hiMemIco : i ∈ Finset.Ico 0 (canonicalBlockStartTime n m - H) := by
    simp only [Finset.mem_Ico, i]
    omega
  rw [canonicalSourceAgeDeficit, canonicalSourceAgeDeficit,
    canonicalOldSourceClaimCarrier_succ_horizon_of_lt_start hH]
  by_cases hiCarry : CarryTwoDebtAt n i
  · have hiMem : i ∈ canonicalOldSourceClaimCarrier n H m := by
      rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff]
      exact ⟨hiMemIco, hiCarry⟩
    have hcard : 1 ≤ (canonicalOldSourceClaimCarrier n H m).card := by
      exact Finset.one_le_card.mpr ⟨i, hiMem⟩
    rw [Finset.card_erase_of_mem hiMem]
    rw [Nat.cast_sub hcard]
    change CarryTwoDebtAt n
      (canonicalBlockStartTime n m - H - 1) at hiCarry
    simp [canonicalCarryTwoIndicator, hiCarry]
    ring
  · have hiNotMem : i ∉ canonicalOldSourceClaimCarrier n H m := by
      intro hi
      exact hiCarry (mem_carryTwoPositions_iff.mp hi).2
    rw [Finset.erase_eq_self.mpr hiNotMem]
    change ¬ CarryTwoDebtAt n
      (canonicalBlockStartTime n m - H - 1) at hiCarry
    simp [canonicalCarryTwoIndicator, hiCarry]

/-- Once the horizon reaches the block start, both adjacent horizon carriers
are empty.  The deficit therefore remains the negative cumulative service. -/
theorem canonicalSourceAgeDeficit_succ_horizon_eq_of_start_le
    {n : OddNat} {H m : ℕ}
    (hH : canonicalBlockStartTime n m ≤ H) :
    canonicalSourceAgeDeficit n (H + 1) m =
      canonicalSourceAgeDeficit n H m := by
  rw [canonicalSourceAgeDeficit,
    canonicalOldSourceClaimCarrier_eq_empty_of_start_le (by omega),
    canonicalSourceAgeDeficit,
    canonicalOldSourceClaimCarrier_eq_empty_of_start_le hH]

/-! ## Exact crossing-window horizon shift -/

/-- Sliding the mature crossing window one source time to the left exchanges
exactly its old upper boundary for its new lower boundary. -/
theorem canonicalSourceAgeHorizonCrossingClaims_succ_union_upper_eq
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    canonicalSourceAgeHorizonCrossingClaims n (H + 1) m ∪
        carryTwoPositions n
          {canonicalBlockStartTime n (m + 1) - H - 1} =
      carryTwoPositions n
          {canonicalBlockStartTime n m - H - 1} ∪
        canonicalSourceAgeHorizonCrossingClaims n H m := by
  classical
  have hstep : canonicalBlockStartTime n m + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [canonicalBlockStartTime_succ]
    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
  ext i
  simp only [canonicalSourceAgeHorizonCrossingClaims,
    mem_carryTwoPositions_iff, Finset.mem_Ico, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · rintro (⟨⟨hiLo, hiHi⟩, hiCarry⟩ | ⟨rfl, hiCarry⟩)
    · by_cases hiLower : i = canonicalBlockStartTime n m - H - 1
      · exact Or.inl ⟨hiLower, hiCarry⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hiCarry⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hiCarry⟩
  · rintro (⟨rfl, hiCarry⟩ | ⟨⟨hiLo, hiHi⟩, hiCarry⟩)
    · exact Or.inl ⟨⟨by omega, by omega⟩, hiCarry⟩
    · by_cases hiUpper : i = canonicalBlockStartTime n (m + 1) - H - 1
      · exact Or.inr ⟨hiUpper, hiCarry⟩
      · exact Or.inl ⟨⟨by omega, by omega⟩, hiCarry⟩

private theorem disjoint_crossing_succ_carry_upper
    {n : OddNat} {H m : ℕ}
    (_hH : H < canonicalBlockStartTime n m) :
    Disjoint (canonicalSourceAgeHorizonCrossingClaims n (H + 1) m)
      (carryTwoPositions n
        {canonicalBlockStartTime n (m + 1) - H - 1}) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiCross hiUpper
  have hiRange := (mem_carryTwoPositions_iff.mp hiCross).1
  have hiEq := (mem_carryTwoPositions_iff.mp hiUpper).1
  simp only [Finset.mem_Ico] at hiRange
  simp only [Finset.mem_singleton] at hiEq
  omega

private theorem disjoint_carry_lower_crossing
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    Disjoint
      (carryTwoPositions n {canonicalBlockStartTime n m - H - 1})
      (canonicalSourceAgeHorizonCrossingClaims n H m) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiLower hiCross
  have hiEq := (mem_carryTwoPositions_iff.mp hiLower).1
  have hiRange := (mem_carryTwoPositions_iff.mp hiCross).1
  simp only [Finset.mem_singleton] at hiEq
  simp only [Finset.mem_Ico] at hiRange
  omega

/-- Exact signed cardinal law for a one-step mature horizon shift. -/
theorem int_card_crossing_succ_horizon_sub_card_crossing
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
        (canonicalSourceAgeHorizonCrossingClaims n H m).card =
      canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n m - H - 1) -
        canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n (m + 1) - H - 1) := by
  have hcarrier :=
    canonicalSourceAgeHorizonCrossingClaims_succ_union_upper_eq hH
  have hcard := congrArg Finset.card hcarrier
  rw [Finset.card_union_of_disjoint (disjoint_crossing_succ_carry_upper hH),
    Finset.card_union_of_disjoint (disjoint_carry_lower_crossing hH),
    card_carryTwoPositions_singleton,
    card_carryTwoPositions_singleton] at hcard
  have hcardInt :
      ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) +
          canonicalCarryTwoIndicator n
            (canonicalBlockStartTime n (m + 1) - H - 1) =
        canonicalCarryTwoIndicator n
            (canonicalBlockStartTime n m - H - 1) +
          (canonicalSourceAgeHorizonCrossingClaims n H m).card := by
    exact_mod_cast hcard
  omega

/-- Actual service is independent of the age horizon, so the frontier's
horizon derivative is exactly the same two-boundary exchange. -/
theorem canonicalSourceAgeFrontierIncrement_succ_horizon_sub
    {n : OddNat} {H m : ℕ}
    (hH : H < canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n (H + 1) m -
        canonicalSourceAgeFrontierIncrement n H m =
      canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n m - H - 1) -
        canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n (m + 1) - H - 1) := by
  unfold canonicalSourceAgeFrontierIncrement
  calc
    ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
          canonicalQueueConsumed n m -
        (((canonicalSourceAgeHorizonCrossingClaims n H m).card : ℤ) -
          canonicalQueueConsumed n m) =
        ((canonicalSourceAgeHorizonCrossingClaims n (H + 1) m).card : ℤ) -
          (canonicalSourceAgeHorizonCrossingClaims n H m).card := by ring
    _ = _ := int_card_crossing_succ_horizon_sub_card_crossing hH

/-! ## Horizon-one block decomposition -/

/-- At positive source time, the age-one crossing carrier consists of the
predecessor source and the current block carrier with its final source
removed. -/
theorem canonicalSourceAgeHorizonCrossingClaims_one_eq
    {n : OddNat} {m : ℕ}
    (hstart : 0 < canonicalBlockStartTime n m) :
    canonicalSourceAgeHorizonCrossingClaims n 1 m =
      carryTwoPositions n {canonicalBlockStartTime n m - 1} ∪
        (canonicalBlockClaimSourceCarrier n m).erase
          (canonicalBlockStartTime n (m + 1) - 1) := by
  classical
  have hstep : canonicalBlockStartTime n m + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [canonicalBlockStartTime_succ]
    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
  ext i
  simp only [canonicalSourceAgeHorizonCrossingClaims,
    canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff,
    Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨hiLo, hiHi⟩, hiCarry⟩
    by_cases hiPred : i = canonicalBlockStartTime n m - 1
    · exact Or.inl ⟨hiPred, hiCarry⟩
    · exact Or.inr ⟨by omega, ⟨⟨by omega, by omega⟩, hiCarry⟩⟩
  · rintro (⟨rfl, hiCarry⟩ | ⟨hiFinal, ⟨⟨hiLo, hiHi⟩, hiCarry⟩⟩)
    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩
    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩

private theorem disjoint_predecessor_erased_block
    {n : OddNat} {m : ℕ}
    (hstart : 0 < canonicalBlockStartTime n m) :
    Disjoint (carryTwoPositions n {canonicalBlockStartTime n m - 1})
      ((canonicalBlockClaimSourceCarrier n m).erase
        (canonicalBlockStartTime n (m + 1) - 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiPred hiBlock
  have hiEq := (mem_carryTwoPositions_iff.mp hiPred).1
  have hiRange := mem_canonicalBlockClaimSourceCarrier_interval
    (Finset.mem_of_mem_erase hiBlock)
  simp only [Finset.mem_singleton] at hiEq
  have hiLo := (Finset.mem_Ico.mp hiRange).1
  omega

/-- Removing the final block source subtracts precisely its carry indicator. -/
theorem card_erase_final_add_indicator_eq_blockClaimSourceCarrier
    (n : OddNat) (m : ℕ) :
    ((canonicalBlockClaimSourceCarrier n m).erase
        (canonicalBlockStartTime n (m + 1) - 1)).card +
      canonicalCarryTwoIndicator n
        (canonicalBlockStartTime n (m + 1) - 1) =
      (canonicalBlockClaimSourceCarrier n m).card := by
  classical
  let i := canonicalBlockStartTime n (m + 1) - 1
  have hstep : canonicalBlockStartTime n m + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [canonicalBlockStartTime_succ]
    exact Nat.add_le_add_left (one_le_canonicalBlockLength n m) _
  by_cases hiCarry : CarryTwoDebtAt n i
  · have hiMem : i ∈ canonicalBlockClaimSourceCarrier n m := by
      rw [canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff]
      exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
    rw [Finset.card_erase_of_mem hiMem]
    change CarryTwoDebtAt n
      (canonicalBlockStartTime n (m + 1) - 1) at hiCarry
    simp [canonicalCarryTwoIndicator, hiCarry]
    have := Finset.one_le_card.mpr ⟨i, hiMem⟩
    omega
  · have hiNotMem : i ∉ canonicalBlockClaimSourceCarrier n m := by
      intro hi
      exact hiCarry (carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi)
    rw [Finset.erase_eq_self.mpr hiNotMem]
    change ¬ CarryTwoDebtAt n
      (canonicalBlockStartTime n (m + 1) - 1) at hiCarry
    simp [canonicalCarryTwoIndicator, hiCarry]

/-- Exact cardinal form of the horizon-one predecessor/block/final split. -/
theorem int_card_sourceAgeHorizonCrossingClaims_one
    {n : OddNat} {m : ℕ}
    (hstart : 0 < canonicalBlockStartTime n m) :
    ((canonicalSourceAgeHorizonCrossingClaims n 1 m).card : ℤ) =
      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) +
        canonicalQueueDemand n m -
          canonicalCarryTwoIndicator n
            (canonicalBlockStartTime n (m + 1) - 1) := by
  have hcarrier := canonicalSourceAgeHorizonCrossingClaims_one_eq hstart
  have hcard := congrArg Finset.card hcarrier
  rw [Finset.card_union_of_disjoint
      (disjoint_predecessor_erased_block hstart),
    card_carryTwoPositions_singleton] at hcard
  have hfinal := card_erase_final_add_indicator_eq_blockClaimSourceCarrier n m
  rw [card_canonicalBlockClaimSourceCarrier] at hfinal
  have hcardInt :
      ((canonicalSourceAgeHorizonCrossingClaims n 1 m).card : ℤ) =
        canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) +
          (((canonicalBlockClaimSourceCarrier n m).erase
            (canonicalBlockStartTime n (m + 1) - 1)).card : ℤ) := by
    exact_mod_cast hcard
  have hfinalInt :
      (((canonicalBlockClaimSourceCarrier n m).erase
          (canonicalBlockStartTime n (m + 1) - 1)).card : ℤ) +
        canonicalCarryTwoIndicator n
          (canonicalBlockStartTime n (m + 1) - 1) =
        canonicalQueueDemand n m := by
    exact_mod_cast hfinal
  omega

/-! ## Saturated horizon-one audit -/

/-- Away from the origin boundary, a saturated block's horizon-one frontier
is exactly the carry indicator of the predecessor source.  The two current
claims contribute two, the final claim leaves the shifted window, and actual
service consumes one. -/
theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_one_eq_indicator
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hstart : 0 < canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n 1 m =
      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
  have hfinalEq : canonicalBlockStartTime n (m + 1) - 1 =
      paymentEndpointSeq n m := by
    calc
      canonicalBlockStartTime n (m + 1) - 1 =
          canonicalBlockStartTime n m + canonicalBlockLength n m - 1 := by
            rw [canonicalBlockStartTime_succ]
      _ = paymentEndpointSeq n m :=
        canonicalBlockStartTime_add_length_sub_one_eq_endpoint n m
  have hendpointMem : paymentEndpointSeq n m ∈ canonicalPaymentBlock n m := by
    rw [canonicalPaymentBlock_eq_sourceFiber]
    exact endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)
  have hfinalCarry : CarryTwoDebtAt n
      (canonicalBlockStartTime n (m + 1) - 1) := by
    rw [hfinalEq]
    exact h.carryTwo_of_mem hendpointMem
  have hfinalIndicator : canonicalCarryTwoIndicator n
      (canonicalBlockStartTime n (m + 1) - 1) = 1 :=
    (canonicalCarryTwoIndicator_eq_one_iff n _).2 hfinalCarry
  unfold canonicalSourceAgeFrontierIncrement
  rw [int_card_sourceAgeHorizonCrossingClaims_one hstart,
    hfinalIndicator, h.canonicalQueueConsumed_eq_one]
  change (canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) : ℤ) +
      (canonicalQueueDemand n m : ℤ) - 1 - 1 = _
  rw [canonicalQueueDemand, h.2.1, h.length_eq_two]
  ring

/-- The origin is a genuine Nat-subtraction exception to the mature formula:
the predecessor `start - 1` aliases source zero instead of lying outside the
current block. -/
theorem sourceAgeFrontierIncrement_one_fiftyNine_zero_eq_zero :
    canonicalSourceAgeFrontierIncrement fiftyNineSaturatedOdd 1 0 = 0 := by
  have hstart0 : canonicalBlockStartTime fiftyNineSaturatedOdd 0 = 0 := rfl
  have hstart1 : canonicalBlockStartTime fiftyNineSaturatedOdd 1 = 2 := by
    rw [canonicalBlockStartTime_succ, hstart0,
      canonicalBlockLength_fiftyNine_zero]
  have hcross : canonicalSourceAgeHorizonCrossingClaims
      fiftyNineSaturatedOdd 1 0 = {0} := by
    classical
    ext i
    rw [canonicalSourceAgeHorizonCrossingClaims,
      mem_carryTwoPositions_iff]
    simp only [hstart0, hstart1, Nat.zero_sub, Nat.reduceSub,
      Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hi⟩, _⟩
      omega
    · intro hi
      subst i
      exact ⟨⟨by omega, by omega⟩, fiftyNine_carry_zero⟩
  unfold canonicalSourceAgeFrontierIncrement
  rw [hcross]
  simp [canonicalSaturatedBorderBlock_fiftyNine_zero.canonicalQueueConsumed_eq_one]

theorem canonicalCarryTwoIndicator_fiftyNine_origin_eq_one :
    canonicalCarryTwoIndicator fiftyNineSaturatedOdd
      (canonicalBlockStartTime fiftyNineSaturatedOdd 0 - 1) = 1 := by
  rw [canonicalCarryTwoIndicator_eq_one_iff]
  simpa using fiftyNine_carry_zero

/-- Therefore the mature saturated `H = 1` formula cannot be extended across
the origin without an explicit early-boundary correction. -/
theorem not_saturated_frontier_one_eq_predecessor_indicator_without_start :
    ¬ ∀ n m, CanonicalSaturatedBorderBlock n m →
      canonicalSourceAgeFrontierIncrement n 1 m =
        canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
  intro h
  have hEq := h fiftyNineSaturatedOdd 0
    canonicalSaturatedBorderBlock_fiftyNine_zero
  rw [sourceAgeFrontierIncrement_one_fiftyNine_zero_eq_zero,
    canonicalCarryTwoIndicator_fiftyNine_origin_eq_one] at hEq
  omega

/-! ## Origin-to-crossing block map -/

/-- Every member of a canonical payment block lies in its exact half-open
source-time interval. -/
theorem mem_canonicalPaymentBlock_startTime_interval
    {n : OddNat} {m i : ℕ} (hi : i ∈ canonicalPaymentBlock n m) :
    i ∈ Finset.Ico (canonicalBlockStartTime n m)
      (canonicalBlockStartTime n (m + 1)) := by
  rw [canonicalPaymentBlock_eq_sourceFiber,
    orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
      (paymentEndpointSeq n m)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)] at hi
  have hiBounds := Finset.mem_Icc.mp hi
  have hstart := canonicalBlockStartTime_eq_universalPaymentBlockStart n m
  have hnext : canonicalBlockStartTime n (m + 1) =
      paymentEndpointSeq n m + 1 := by
    simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
  exact Finset.mem_Ico.mpr ⟨by simpa [hstart] using hiBounds.1,
    by omega⟩

/-- The unique canonical block containing source time `i + H`. -/
noncomputable def canonicalAgeCrossingBlockOfSource
    (n : OddNat) (H i : ℕ) : ℕ :=
  Classical.choose (existsUnique_mem_canonicalPaymentBlock n (i + H))

theorem shiftedSource_mem_canonicalAgeCrossingBlockOfSource
    (n : OddNat) (H i : ℕ) :
    i + H ∈ canonicalPaymentBlock n
      (canonicalAgeCrossingBlockOfSource n H i) :=
  (Classical.choose_spec
    (existsUnique_mem_canonicalPaymentBlock n (i + H))).1

/-- Subject to the exact non-underflow condition, a carry-two source belongs
to the age-`H` crossing carrier of the block containing its shifted source
time. -/
theorem mem_crossingClaims_canonicalAgeCrossingBlockOfSource
    {n : OddNat} {H i : ℕ} (hiCarry : CarryTwoDebtAt n i)
    (hboundary : H ≤ canonicalBlockStartTime n
      (canonicalAgeCrossingBlockOfSource n H i)) :
    i ∈ canonicalSourceAgeHorizonCrossingClaims n H
      (canonicalAgeCrossingBlockOfSource n H i) := by
  let m := canonicalAgeCrossingBlockOfSource n H i
  change H ≤ canonicalBlockStartTime n m at hboundary
  have hiBlock : i + H ∈ canonicalPaymentBlock n m := by
    exact shiftedSource_mem_canonicalAgeCrossingBlockOfSource n H i
  have hiRange := Finset.mem_Ico.mp
    (mem_canonicalPaymentBlock_startTime_interval hiBlock)
  have hmono : canonicalBlockStartTime n m ≤
      canonicalBlockStartTime n (m + 1) :=
    canonicalBlockStartTime_mono n (by omega)
  have hnextBoundary : H ≤ canonicalBlockStartTime n (m + 1) :=
    hboundary.trans hmono
  have hleftEq := Nat.sub_add_cancel hboundary
  have hrightEq := Nat.sub_add_cancel hnextBoundary
  change i ∈ canonicalSourceAgeHorizonCrossingClaims n H m
  rw [canonicalSourceAgeHorizonCrossingClaims,
    mem_carryTwoPositions_iff]
  exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩

/-! ## Short-window frontier sums -/

/-- Signed frontier flow through a consecutive finite block-index window. -/
noncomputable def canonicalSourceAgeFrontierWindowSum
    (n : OddNat) (H q L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, canonicalSourceAgeFrontierIncrement n H (q + j)

/-- Every finite frontier window telescopes to the change in signed deficit. -/
theorem canonicalSourceAgeFrontierWindowSum_eq_deficit_sub
    (n : OddNat) (H q L : ℕ) :
    canonicalSourceAgeFrontierWindowSum n H q L =
      canonicalSourceAgeDeficit n H (q + L) -
        canonicalSourceAgeDeficit n H q := by
  induction L with
  | zero => simp [canonicalSourceAgeFrontierWindowSum]
  | succ L ih =>
      rw [canonicalSourceAgeFrontierWindowSum, Finset.sum_range_succ]
      change canonicalSourceAgeFrontierWindowSum n H q L +
          canonicalSourceAgeFrontierIncrement n H (q + L) = _
      have hq : q + (L + 1) = (q + L) + 1 := by omega
      rw [ih, hq, canonicalSourceAgeDeficit_succ]
      ring

@[simp] theorem canonicalSourceAgeFrontierWindowSum_zero
    (n : OddNat) (H q : ℕ) :
    canonicalSourceAgeFrontierWindowSum n H q 0 = 0 := by
  simp [canonicalSourceAgeFrontierWindowSum]

@[simp] theorem canonicalSourceAgeFrontierWindowSum_one
    (n : OddNat) (H q : ℕ) :
    canonicalSourceAgeFrontierWindowSum n H q 1 =
      canonicalSourceAgeFrontierIncrement n H q := by
  simp [canonicalSourceAgeFrontierWindowSum]

@[simp] theorem canonicalSourceAgeFrontierWindowSum_two
    (n : OddNat) (H q : ℕ) :
    canonicalSourceAgeFrontierWindowSum n H q 2 =
      canonicalSourceAgeFrontierIncrement n H q +
        canonicalSourceAgeFrontierIncrement n H (q + 1) := by
  simp [canonicalSourceAgeFrontierWindowSum, Finset.sum_range_succ]

/-- The shortest horizon-zero window at a saturated block has total `+1`. -/
theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_zero_one
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalSourceAgeFrontierWindowSum n 0 m 1 = 1 := by
  rw [canonicalSourceAgeFrontierWindowSum_one,
    h.sourceAgeFrontierIncrement_zero_eq_one]

/-- At positive block start, the shortest horizon-one saturated window is
exactly the predecessor carry indicator. -/
theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_one_one
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hstart : 0 < canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierWindowSum n 1 m 1 =
      canonicalCarryTwoIndicator n (canonicalBlockStartTime n m - 1) := by
  rw [canonicalSourceAgeFrontierWindowSum_one,
    h.sourceAgeFrontierIncrement_one_eq_indicator hstart]

/-! ## Saturated-successor actual-consumption bridge -/

/-- Saturation leaves at least one queued claim for the successor, while every
canonical successor offers at least one service slot.  Thus the successor's
*actual* consumption is positive.  This conclusion uses queue conservation;
it is not obtained by substituting endpoint capacity for actual service. -/
theorem CanonicalSaturatedBorderBlock.successor_queueConsumed_pos
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    0 < canonicalQueueConsumed n (m + 1) := by
  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
    rw [h.queueBeforeBlock_succ_eq_add_one]
    omega
  have havailable : 1 ≤
      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
        canonicalQueueDemand n (m + 1) := by omega
  have hservice : 1 ≤ canonicalQueueService n (m + 1) := by
    unfold canonicalQueueService
    rw [canonicalBlockCapacityCount_eq_terminalValuation]
    exact one_le_canonicalBlockTerminalValuation n (m + 1)
  unfold canonicalQueueConsumed
  exact lt_of_lt_of_le Nat.zero_lt_one (le_min havailable hservice)

/-- If the successor has strictly negative endpoint drift, its extra service
slot is actually consumed, so the saturated `+1` is repaid within the exact
two-block horizon-zero window.  Nonpositive drift is insufficient: zero drift
can leave the two-block sum positive, as the bounded audit records. -/
theorem
    CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_negative
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hnegative : endpointAccountingTerm n (m + 1) < 0) :
    canonicalSourceAgeFrontierWindowSum n 0 m 2 ≤ 0 := by
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
    n (m + 1)
  change endpointAccountingTerm n (m + 1) =
      (canonicalQueueDemand n (m + 1) : ℤ) -
        canonicalQueueService n (m + 1) at hdrift
  have hservice : canonicalQueueDemand n (m + 1) + 1 ≤
      canonicalQueueService n (m + 1) := by omega
  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
    rw [h.queueBeforeBlock_succ_eq_add_one]
    omega
  have havailable : canonicalQueueDemand n (m + 1) + 1 ≤
      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
        canonicalQueueDemand n (m + 1) := by omega
  have hconsumed : canonicalQueueDemand n (m + 1) + 1 ≤
      canonicalQueueConsumed n (m + 1) := by
    unfold canonicalQueueConsumed
    exact le_min havailable hservice
  rw [canonicalSourceAgeFrontierWindowSum_two,
    h.sourceAgeFrontierIncrement_zero_eq_one,
    canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed]
  omega

/-!
## Conditional challenge-facing boundary

The positive route now has an exact public chain:

1. externally construct a noncircular
   `CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature`;
2. obtain all nonpositive frontier prefixes;
3. obtain uniform actual source age `H`;
4. obtain queue bound `H` and endpoint-width bound `bitWidth n + H`.

This module does **not** construct such a signature/certificate or prove that
some horizon `H` works.  The bounded audit is discovery evidence only.  The
saturated-successor split supplies positive successor consumption, and its
strictly-negative branch supplies a two-block repayment theorem, but the
zero-drift and positive-pressure branches do not currently give the uniform
window consumption lower bound required for the global certificate.
-/

end DkMath.Collatz
