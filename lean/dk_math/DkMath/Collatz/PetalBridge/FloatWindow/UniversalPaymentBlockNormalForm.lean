/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm"

namespace DkMath.Collatz

/-!
# Exact arithmetic normal form of a canonical payment block

This module exposes the arithmetic hidden by the source-fiber geometry.  A
canonical block starts at an odd state `x` whose all-ones depth is its block
length `L`.  Removing that exact power of two gives an odd core `u`.  The
height-one interior then evolves by an exact affine recurrence, and the next
block starts at the odd part of `3^L * u - 1`.

No logarithmic or asymptotic approximation is used here.
-/

/-- Proof-independent orbit time at which canonical block `k` starts. -/
noncomputable def canonicalBlockStartTime (n : OddNat) (k : ℕ) : ℕ :=
  canonicalEndpointBlockStart n k

/-- Odd state at the start of canonical block `k`. -/
noncomputable def canonicalBlockStartState (n : OddNat) (k : ℕ) : ℕ :=
  (iterateT (canonicalBlockStartTime n k) n).1

/-- Length of canonical block `k`. -/
noncomputable def canonicalBlockLength (n : OddNat) (k : ℕ) : ℕ :=
  canonicalPaymentBlockLength n k

/-- Odd core obtained by removing the exact block-length power of two. -/
noncomputable def canonicalBlockOddCore (n : OddNat) (k : ℕ) : ℕ :=
  (canonicalBlockStartState n k + 1) / 2 ^ canonicalBlockLength n k

/-- State at the final source time of canonical block `k`. -/
noncomputable def canonicalBlockEndpointState (n : OddNat) (k : ℕ) : ℕ :=
  (iterateT (paymentEndpointSeq n k) n).1

/-- State immediately after canonical block `k` has completed. -/
noncomputable def canonicalBlockNextStartState (n : OddNat) (k : ℕ) : ℕ :=
  (iterateT (paymentEndpointSeq n k + 1) n).1

/-- Terminal arithmetic carrier whose odd part starts the next block. -/
noncomputable def canonicalBlockTerminalCarrier (n : OddNat) (k : ℕ) : ℕ :=
  3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k - 1

/-- Terminal 2-adic valuation removed at the endpoint transition. -/
noncomputable def canonicalBlockTerminalValuation (n : OddNat) (k : ℕ) : ℕ :=
  v2 (canonicalBlockTerminalCarrier n k)

/-- Every canonical block contains at least its endpoint source. -/
theorem one_le_canonicalBlockLength (n : OddNat) (k : ℕ) :
    1 ≤ canonicalBlockLength n k := by
  exact canonicalPaymentBlockLength_pos n k

/-- The proof-independent start is the universal source-fiber minimum. -/
theorem canonicalBlockStartTime_eq_universalPaymentBlockStart
    (n : OddNat) (k : ℕ) :
    canonicalBlockStartTime n k =
      universalPaymentBlockStart n (paymentEndpointSeq n k)
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) := by
  exact canonicalEndpointBlockStart_eq_universalPaymentBlockStart n k

/-- The start time is no later than its canonical endpoint. -/
theorem canonicalBlockStartTime_le_endpoint (n : OddNat) (k : ℕ) :
    canonicalBlockStartTime n k ≤ paymentEndpointSeq n k := by
  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
  exact (mem_orbitPaymentSourceFiberAt_iff.mp
    (universalPaymentBlockStart_mem_sourceFiber n (paymentEndpointSeq n k)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))).1

/-- Block length is the exact all-ones depth of the start state. -/
theorem canonicalBlockLength_eq_v2_startState_add_one
    (n : OddNat) (k : ℕ) :
    canonicalBlockLength n k = v2 (canonicalBlockStartState n k + 1) := by
  unfold canonicalBlockLength canonicalBlockStartState canonicalBlockStartTime
  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
  rw [orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_start n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
  simp [orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
    canonicalEndpointBlockStart_eq_universalPaymentBlockStart]

/-- The start word plus one is exactly `2^L` times the odd block core. -/
theorem canonicalBlockStartState_add_one_eq_pow_mul_oddCore
    (n : OddNat) (k : ℕ) :
    canonicalBlockStartState n k + 1 =
      2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
  unfold canonicalBlockOddCore
  rw [canonicalBlockLength_eq_v2_startState_add_one]
  exact (Nat.mul_div_cancel' (by
    simpa [v2] using
      (pow_padicValNat_dvd
        (p := 2) (n := canonicalBlockStartState n k + 1)))).symm

/-- Removing the maximal two-power from a positive natural leaves an odd word. -/
private theorem div_pow_v2_mod_two_eq_one {a : ℕ} (ha : 0 < a) :
    (a / 2 ^ v2 a) % 2 = 1 := by
  let u := a / 2 ^ v2 a
  have hdvd : 2 ^ v2 a ∣ a := by
    simpa [v2] using (pow_padicValNat_dvd (p := 2) (n := a))
  have haeq : a = 2 ^ v2 a * u := by
    simpa [u] using (Nat.mul_div_cancel' hdvd).symm
  rcases Nat.mod_two_eq_zero_or_one u with hu | hu
  · have htwo : 2 ∣ u := Nat.dvd_iff_mod_eq_zero.mpr hu
    rcases htwo with ⟨w, huw⟩
    have hsucc : 2 ^ (v2 a + 1) ∣ a := by
      refine ⟨w, ?_⟩
      calc
        a = 2 ^ v2 a * u := haeq
        _ = 2 ^ v2 a * (2 * w) := by rw [huw]
        _ = 2 ^ (v2 a + 1) * w := by rw [pow_succ]; ring
    have hnot : ¬ 2 ^ (v2 a + 1) ∣ a := by
      simpa [v2] using (pow_succ_padicValNat_not_dvd ha.ne')
    exact (hnot hsucc).elim
  · exact hu

/-- The canonical block core is odd. -/
theorem canonicalBlockOddCore_mod_two_eq_one (n : OddNat) (k : ℕ) :
    canonicalBlockOddCore n k % 2 = 1 := by
  unfold canonicalBlockOddCore
  rw [canonicalBlockLength_eq_v2_startState_add_one]
  apply div_pow_v2_mod_two_eq_one
  omega

/-- The canonical block core is positive. -/
theorem canonicalBlockOddCore_pos (n : OddNat) (k : ℕ) :
    0 < canonicalBlockOddCore n k := by
  have hodd := canonicalBlockOddCore_mod_two_eq_one n k
  omega

/-- One exact height-one orbit step in add-one coordinates. -/
theorem two_mul_iterateT_succ_add_one_eq_three_mul_iterateT_add_one
    (n : OddNat) (i : ℕ) (hheight : orbitWindowHeight n i = 1) :
    2 * ((iterateT (i + 1) n).1 + 1) =
      3 * ((iterateT i n).1 + 1) := by
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  have hraw := threeNPlusOne_eq_pow_height_mul_T (iterateT i n)
  rw [hs] at hraw
  rw [iterateT_succ_eq_T_iterateT]
  simp [threeNPlusOne] at hraw
  omega

/-- The canonical endpoint is `start + L - 1`. -/
theorem canonicalBlockStartTime_add_length_sub_one_eq_endpoint
    (n : OddNat) (k : ℕ) :
    canonicalBlockStartTime n k + canonicalBlockLength n k - 1 =
      paymentEndpointSeq n k := by
  rw [canonicalBlockLength]
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one]
  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
  have hle := canonicalBlockStartTime_le_endpoint n k
  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart] at hle
  omega

/-- Exact multiplicative trajectory throughout a completed canonical block. -/
theorem canonicalBlock_iterate_add_one_normal_form
    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
    2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1) =
      3 ^ t * (canonicalBlockStartState n k + 1) := by
  induction t with
  | zero => simp [canonicalBlockStartState]
  | succ t ih =>
      have htPrev : t < canonicalBlockLength n k := by omega
      have htInterior : t < canonicalBlockLength n k - 1 := by omega
      have hstartExact : OrbitDepthRecoversExactlyAt n
          (canonicalBlockStartTime n k) (canonicalBlockLength n k) := by
        simp [OrbitDepthRecoversExactlyAt, ResidualAllOnesDepth,
          oddOrbitLabel, canonicalBlockLength_eq_v2_startState_add_one,
          canonicalBlockStartState]
      have hheight :=
        (orbitDepthRecoversExactlyAt_prePayment_chain n
          (canonicalBlockStartTime n k) (canonicalBlockLength n k)
          (by omega) hstartExact).1 t htInterior |>.2
      have hstep := two_mul_iterateT_succ_add_one_eq_three_mul_iterateT_add_one
        n (canonicalBlockStartTime n k + t) hheight
      rw [show canonicalBlockStartTime n k + (t + 1) =
        (canonicalBlockStartTime n k + t) + 1 by omega]
      rw [pow_succ, pow_succ]
      calc
        2 ^ t * 2 * ((iterateT ((canonicalBlockStartTime n k + t) + 1) n).1 + 1) =
            2 ^ t *
              (2 * ((iterateT ((canonicalBlockStartTime n k + t) + 1) n).1 + 1)) := by
          ring
        _ = 2 ^ t *
              (3 * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1)) := by
          rw [hstep]
        _ = 3 *
              (2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1)) := by
          ring
        _ = 3 * (3 ^ t * (canonicalBlockStartState n k + 1)) := by
          rw [ih htPrev]
        _ = 3 ^ t * 3 * (canonicalBlockStartState n k + 1) := by
          ring

/-- Division-free state formula in block-core coordinates. -/
theorem canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore
    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
    2 ^ t * ((iterateT (canonicalBlockStartTime n k + t) n).1 + 1) =
      3 ^ t * (2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k) := by
  rw [canonicalBlock_iterate_add_one_normal_form n k t ht,
    canonicalBlockStartState_add_one_eq_pow_mul_oddCore]

/-- Exact endpoint state in canonical block-core coordinates. -/
theorem canonicalBlockEndpointState_add_one_eq
    (n : OddNat) (k : ℕ) :
    canonicalBlockEndpointState n k + 1 =
      2 * 3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k := by
  have hL := one_le_canonicalBlockLength n k
  have h := canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore
    n k (canonicalBlockLength n k - 1) (by omega)
  have hindex :
      canonicalBlockStartTime n k + (canonicalBlockLength n k - 1) =
        paymentEndpointSeq n k := by
    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
    omega
  rw [hindex] at h
  unfold canonicalBlockEndpointState
  have hpow : 2 ^ canonicalBlockLength n k =
      2 ^ (canonicalBlockLength n k - 1) * 2 := by
    conv_lhs => rw [show canonicalBlockLength n k =
      (canonicalBlockLength n k - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow] at h
  have htwoPos : 0 < 2 ^ (canonicalBlockLength n k - 1) := pow_pos (by omega) _
  nlinarith

/-- Raw endpoint transition before its terminal two-adic payment. -/
theorem three_mul_canonicalBlockEndpointState_add_one_eq
    (n : OddNat) (k : ℕ) :
    3 * canonicalBlockEndpointState n k + 1 =
      2 * canonicalBlockTerminalCarrier n k := by
  unfold canonicalBlockTerminalCarrier
  have hend := canonicalBlockEndpointState_add_one_eq n k
  have hL := one_le_canonicalBlockLength n k
  have hpow : 3 ^ canonicalBlockLength n k =
      3 ^ (canonicalBlockLength n k - 1) * 3 := by
    conv_lhs => rw [show canonicalBlockLength n k =
      (canonicalBlockLength n k - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  have hu := canonicalBlockOddCore_pos n k
  have hcarrier :
      3 ^ (canonicalBlockLength n k - 1) * 3 * canonicalBlockOddCore n k =
        3 * (3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k) := by
    ring
  rw [hcarrier]
  have hend' : canonicalBlockEndpointState n k + 1 =
      2 * (3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k) := by
    simpa [mul_assoc] using hend
  have hfactor : 0 <
      3 ^ (canonicalBlockLength n k - 1) * canonicalBlockOddCore n k :=
    Nat.mul_pos (pow_pos (by omega) _) hu
  omega

/-- The terminal carrier is positive. -/
theorem canonicalBlockTerminalCarrier_pos (n : OddNat) (k : ℕ) :
    0 < canonicalBlockTerminalCarrier n k := by
  unfold canonicalBlockTerminalCarrier
  have hL := one_le_canonicalBlockLength n k
  have hu := canonicalBlockOddCore_pos n k
  have hpow : 3 ≤ 3 ^ canonicalBlockLength n k := by
    have hbase : 0 < (3 : ℕ) := by omega
    exact Nat.pow_le_pow_right hbase hL
  have hproduct : 3 ≤
      3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
    calc
      3 ≤ 3 ^ canonicalBlockLength n k := hpow
      _ = 3 ^ canonicalBlockLength n k * 1 := by simp
      _ ≤ 3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k :=
        Nat.mul_le_mul_left _ hu
  omega

/-- The endpoint height is one plus the terminal carrier valuation. -/
theorem canonicalBlock_endpointHeight_eq_terminalValuation_add_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeight n (paymentEndpointSeq n k) =
      canonicalBlockTerminalValuation n k + 1 := by
  rw [orbitWindowHeight_eq_s_iterateT]
  unfold s canonicalBlockTerminalValuation
  change v2 (threeNPlusOne (canonicalBlockEndpointState n k)) =
    v2 (canonicalBlockTerminalCarrier n k) + 1
  have hraw := three_mul_canonicalBlockEndpointState_add_one_eq n k
  have hraw' : threeNPlusOne (canonicalBlockEndpointState n k) =
      2 * canonicalBlockTerminalCarrier n k := by
    simpa [threeNPlusOne] using hraw
  rw [hraw']
  have hv := (DkMath.ABC.padic_val_two_of_even
    (canonicalBlockTerminalCarrier n k)).2
      (canonicalBlockTerminalCarrier_pos n k).ne'
  simpa [v2, Nat.add_comm] using hv

/-- Canonical anonymous capacity is exactly the terminal 2-adic valuation. -/
theorem canonicalBlockCapacityCount_eq_terminalValuation
    (n : OddNat) (k : ℕ) :
    canonicalBlockCapacityCount n k = canonicalBlockTerminalValuation n k := by
  unfold canonicalBlockCapacityCount
  rw [canonicalEndpointCapacitySlots_card]
  unfold extraPaymentCapacityAt
  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one]
  omega

/-- The next canonical start is the odd part of the terminal carrier. -/
theorem canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
    (n : OddNat) (k : ℕ) :
    canonicalBlockNextStartState n k =
      canonicalBlockTerminalCarrier n k /
        2 ^ canonicalBlockTerminalValuation n k := by
  unfold canonicalBlockNextStartState
  rw [iterateT_succ_eq_T_iterateT]
  change threeNPlusOne (canonicalBlockEndpointState n k) /
      2 ^ v2 (threeNPlusOne (canonicalBlockEndpointState n k)) =
    canonicalBlockTerminalCarrier n k /
      2 ^ canonicalBlockTerminalValuation n k
  have hraw := three_mul_canonicalBlockEndpointState_add_one_eq n k
  have hraw' : threeNPlusOne (canonicalBlockEndpointState n k) =
      2 * canonicalBlockTerminalCarrier n k := by
    simpa [threeNPlusOne] using hraw
  rw [hraw']
  have hv : v2 (2 * canonicalBlockTerminalCarrier n k) =
      1 + v2 (canonicalBlockTerminalCarrier n k) := by
    simpa [v2] using (DkMath.ABC.padic_val_two_of_even
      (canonicalBlockTerminalCarrier n k)).2
        (canonicalBlockTerminalCarrier_pos n k).ne'
  rw [hv]
  rw [pow_add]
  unfold canonicalBlockTerminalValuation
  change 2 * canonicalBlockTerminalCarrier n k /
      (2 * 2 ^ v2 (canonicalBlockTerminalCarrier n k)) =
    canonicalBlockTerminalCarrier n k /
      2 ^ v2 (canonicalBlockTerminalCarrier n k)
  exact Nat.mul_div_mul_left _ _ (by omega)

/-! ## Exact block-drift consequences -/

/-- Complete carry-two claims form a subfamily of the canonical block. -/
theorem canonicalBlockClaimCount_le_length (n : OddNat) (k : ℕ) :
    canonicalBlockClaimCount n k ≤ canonicalBlockLength n k := by
  classical
  unfold canonicalBlockClaimCount canonicalBlockLength
  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
  rw [carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
  exact Finset.card_filter_le _ _

/-- Signed block drift is bounded by length minus endpoint capacity. -/
theorem endpointAccountingTerm_le_length_sub_capacity
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k ≤
      (canonicalBlockLength n k : ℤ) - canonicalBlockCapacityCount n k := by
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
  exact sub_le_sub_right
    (Int.ofNat_le.mpr (canonicalBlockClaimCount_le_length n k)) _

/-- Positive block drift forces terminal service capacity below block length. -/
theorem canonicalBlockCapacityCount_lt_length_of_endpointAccountingTerm_pos
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    canonicalBlockCapacityCount n k < canonicalBlockLength n k := by
  have hle := endpointAccountingTerm_le_length_sub_capacity n k
  omega

/-- Normal-form reading: positive drift forces `v₂(3^L*u-1) < L`. -/
theorem canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    canonicalBlockTerminalValuation n k < canonicalBlockLength n k := by
  rw [← canonicalBlockCapacityCount_eq_terminalValuation]
  exact canonicalBlockCapacityCount_lt_length_of_endpointAccountingTerm_pos hpos

/-- Positive canonical drift cannot occur without delayed interior debt. -/
theorem canonicalBlockGrowthDebtFiber_nonempty_of_endpointAccountingTerm_pos
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).Nonempty := by
  apply floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos
    n (paymentEndpointSeq n k)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
  rwa [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]

/-! ## Exact in-block overshoot -/

/-- Width is nondecreasing at every height-one interior step of a canonical block. -/
theorem canonicalBlockInterior_bitWidth_le_succ
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k) (paymentEndpointSeq n k)) :
    bitWidth (iterateT i n).1 ≤ bitWidth (iterateT (i + 1) n).1 := by
  have hnonempty := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  have hheight : orbitWindowHeight n i = 1 := by
    apply orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
    simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT i n)
  have hpos : 0 < (iterateT i n).1 := by
    have hodd := (iterateT i n).2
    omega
  have hcarry := stateUpperCarry_one_or_two hpos
  rw [iterateT_succ_eq_T_iterateT]
  omega

/-- The endpoint-before-payment width is the maximum width attained inside the block. -/
theorem canonicalBlock_bitWidth_le_endpoint
    (n : OddNat) (k t : ℕ) (ht : t < canonicalBlockLength n k) :
    bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
      bitWidth (canonicalBlockEndpointState n k) := by
  have hL := one_le_canonicalBlockLength n k
  have htLast : t ≤ canonicalBlockLength n k - 1 := by omega
  have hspan : ∀ d,
      t + d ≤ canonicalBlockLength n k - 1 →
        bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
          bitWidth (iterateT (canonicalBlockStartTime n k + (t + d)) n).1 := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro htd
        have hprev := ih (by omega)
        have hstep := canonicalBlockInterior_bitWidth_le_succ
          (n := n) (k := k) (i := canonicalBlockStartTime n k + (t + d))
          (Finset.mem_Ico.mpr ⟨by omega, by
            have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
            omega⟩)
        rw [show canonicalBlockStartTime n k + (t + (d + 1)) =
          (canonicalBlockStartTime n k + (t + d)) + 1 by omega]
        exact hprev.trans hstep
  have hlast := hspan (canonicalBlockLength n k - 1 - t) (by omega)
  have hindex :
      canonicalBlockStartTime n k +
          (t + (canonicalBlockLength n k - 1 - t)) =
        paymentEndpointSeq n k := by
    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
    omega
  rw [hindex] at hlast
  exact hlast

/-- Interior extra-height capacity is zero before the endpoint payment. -/
theorem shiftedExtraPaymentCapacity_canonicalBlockInterior_eq_zero
    (n : OddNat) (k : ℕ) :
    shiftedExtraPaymentCapacity n (canonicalBlockStartTime n k)
      (paymentEndpointSeq n k - canonicalBlockStartTime n k) = 0 := by
  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico]
  have hindex : canonicalBlockStartTime n k +
      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
        paymentEndpointSeq n k := by
    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
  rw [hindex]
  unfold extraPaymentCapacityOn
  apply Finset.sum_eq_zero
  intro i hi
  have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
    (n := n) (j := paymentEndpointSeq n k)
    (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
    (by simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi)
  rw [hheight]
  rfl

/-- Interior carry-two count is exactly the delayed-debt cardinality. -/
theorem shiftedOrbitCarryTwoCount_canonicalBlockInterior_eq_growthDebt_card
    (n : OddNat) (k : ℕ) :
    shiftedOrbitCarryTwoCount n (canonicalBlockStartTime n k)
      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
        (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
  have hindex : canonicalBlockStartTime n k +
      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
        paymentEndpointSeq n k := by
    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
  calc
    shiftedOrbitCarryTwoCount n (canonicalBlockStartTime n k)
        (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
        (shiftedCarryTwoOffsets n (canonicalBlockStartTime n k)
          (paymentEndpointSeq n k - canonicalBlockStartTime n k)).card :=
      shiftedOrbitCarryTwoCount_eq_offset_card _ _ _
    _ = (carryTwoPositions n (Finset.Ico (canonicalBlockStartTime n k)
          (canonicalBlockStartTime n k +
            (paymentEndpointSeq n k - canonicalBlockStartTime n k)))).card :=
      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card _ _ _
    _ = (carryTwoPositions n (Finset.Ico (canonicalBlockStartTime n k)
          (paymentEndpointSeq n k))).card := by rw [hindex]
    _ = (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
      congr 1
      ext i
      rw [mem_carryTwoPositions_iff,
        mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
          (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
      simp [canonicalBlockStartTime_eq_universalPaymentBlockStart]

/-- Exact in-block burst: endpoint width gain equals delayed interior claims. -/
theorem canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card
    (n : OddNat) (k : ℕ) :
    bitWidth (canonicalBlockEndpointState n k) =
      bitWidth (canonicalBlockStartState n k) +
        (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
  have hledger := bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
    n (canonicalBlockStartTime n k)
      (paymentEndpointSeq n k - canonicalBlockStartTime n k)
  have hindex : canonicalBlockStartTime n k +
      (paymentEndpointSeq n k - canonicalBlockStartTime n k) =
        paymentEndpointSeq n k := by
    exact Nat.add_sub_of_le (canonicalBlockStartTime_le_endpoint n k)
  rw [hindex,
    shiftedExtraPaymentCapacity_canonicalBlockInterior_eq_zero,
    shiftedOrbitCarryTwoCount_canonicalBlockInterior_eq_growthDebt_card] at hledger
  simpa [canonicalBlockEndpointState, canonicalBlockStartState] using hledger

/-- Subtractive form of the exact in-block burst identity. -/
theorem canonicalBlockEndpoint_bitWidth_sub_start_eq_growthDebt_card
    (n : OddNat) (k : ℕ) :
    bitWidth (canonicalBlockEndpointState n k) -
        bitWidth (canonicalBlockStartState n k) =
      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
  rw [canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card]
  omega

/-- Uniform ceiling on the delayed-debt burst produced inside each canonical block. -/
def CanonicalBlockBurstUniformUpperBound (n : OddNat) (D : ℕ) : Prop :=
  ∀ k, (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card ≤ D

/-- A queue ceiling controls every canonical block-start width. -/
theorem canonicalBlockStart_bitWidth_le_of_queueUniformUpperBound
    {n : OddNat} {C : ℕ}
    (hqueue : CanonicalOutstandingClaimQueueUniformUpperBound n C) (k : ℕ) :
    bitWidth (canonicalBlockStartState n k) ≤ bitWidth n.1 + C := by
  cases k with
  | zero =>
      unfold canonicalBlockStartState canonicalBlockStartTime
      simp [canonicalEndpointBlockStart, iterateT]
  | succ k =>
      have hendpoint :=
        hqueue.to_endpointWidthUniformUpperBound k
      unfold canonicalBlockStartState canonicalBlockStartTime
      simpa [canonicalEndpointBlockStart, canonicalEndpointWidth] using hendpoint

/-- Queue drawup plus in-block burst bounds every state inside a canonical block. -/
theorem canonicalBlock_bitWidth_le_of_queue_and_burst_bounds
    {n : OddNat} {C D k t : ℕ}
    (hqueue : CanonicalOutstandingClaimQueueUniformUpperBound n C)
    (hburst : CanonicalBlockBurstUniformUpperBound n D)
    (ht : t < canonicalBlockLength n k) :
    bitWidth (iterateT (canonicalBlockStartTime n k + t) n).1 ≤
      bitWidth n.1 + C + D := by
  have hmax := canonicalBlock_bitWidth_le_endpoint n k t ht
  have hend := canonicalBlockEndpoint_bitWidth_eq_start_add_growthDebt_card n k
  have hstart := canonicalBlockStart_bitWidth_le_of_queueUniformUpperBound hqueue k
  have hdebt := hburst k
  omega

/-!
This is the precise two-coordinate conditional bound available at this layer.
It ranges over every state *inside a named canonical block*.  Promoting it to
an unqualified all-time orbit theorem requires a separate coverage theorem
showing that the canonical block family covers every natural orbit index; that
coverage statement is intentionally not smuggled into the burst argument.
-/

/-!
The completed arithmetic transition is therefore exact:

`(L, u) ↦ oddPart (3^L * u - 1)`.

The terminal valuation is not an auxiliary estimate.  It is definitionally
the endpoint service capacity after the preceding theorem, so later drift
arguments can compare `L` and this valuation without translating between two
independent coordinate systems.
-/

end DkMath.Collatz
