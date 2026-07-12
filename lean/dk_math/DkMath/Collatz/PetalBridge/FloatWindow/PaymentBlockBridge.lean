/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge"

namespace DkMath.Collatz

/-!
# Canonical first-payment blocks

`FloatDebtPaymentDischarge` is retained as a proof-carrying name for backward
compatibility.  The target it proves is a canonical *first payment claim*, not
an allocation statement: a target fiber can be larger than that endpoint's
extra-height capacity.  This module makes the entire first-claim block visible
before any final allocation or transport theorem is attempted.
-/

/-- The canonical first source of a nonempty delayed-growth target fiber. -/
noncomputable def floatPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : ℕ :=
  (floatGrowthDebtFiberAt n j).min' h

/-- The height-one part of a canonical payment block. -/
noncomputable def floatPaymentBlockInterior
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : Finset ℕ :=
  Finset.Ico (floatPaymentBlockStart n j h) j

/-- The complete canonical payment block, including its payment endpoint. -/
noncomputable def floatPaymentBlockWithEndpoint
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) : Finset ℕ :=
  Finset.Icc (floatPaymentBlockStart n j h) j

/-- The carry-two subfamily of a finite collection of orbit times. -/
noncomputable def carryTwoPositions (n : OddNat) (S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter (CarryTwoDebtAt n)

/-- Membership in a finite carry-two subfamily. -/
theorem mem_carryTwoPositions_iff
    {n : OddNat} {S : Finset ℕ} {i : ℕ} :
    i ∈ carryTwoPositions n S ↔ i ∈ S ∧ CarryTwoDebtAt n i := by
  classical
  simp [carryTwoPositions]

/-- The canonical block start is a delayed-growth debt targeting its endpoint. -/
theorem floatPaymentBlockStart_mem_growthDebtFiber
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    floatPaymentBlockStart n j h ∈ floatGrowthDebtFiberAt n j :=
  Finset.min'_mem _ h

/-- The canonical block start carries the endpoint as its first-payment target. -/
theorem floatPaymentBlockStart_target_eq
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    floatDebtPaymentTarget n (floatPaymentBlockStart n j h) = j :=
  (mem_floatGrowthDebtFiberAt_iff.mp
    (floatPaymentBlockStart_mem_growthDebtFiber n j h)).2.2

/-- The canonical block start is strictly before its payment endpoint. -/
theorem floatPaymentBlockStart_lt_endpoint
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    floatPaymentBlockStart n j h < j :=
  lt_of_mem_floatGrowthDebtFiberAt (floatPaymentBlockStart_mem_growthDebtFiber n j h)

/-- The canonical block has exact height one on every interior time. -/
theorem orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
    {n : OddNat} {j t : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
    (ht : t ∈ floatPaymentBlockInterior n j h) :
    orbitWindowHeight n t = 1 := by
  rcases Finset.mem_Ico.mp ht with ⟨hstart, htj⟩
  let a := floatPaymentBlockStart n j h
  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
  have htarget : floatDebtPaymentTarget n a = j :=
    floatPaymentBlockStart_target_eq n j h
  have hdepth := two_le_orbitExactDepth_of_floatDebtAt hdebt
  have hexact : OrbitDepthRecoversExactlyAt n a (orbitExactDepth n a) := by rfl
  rcases orbitDepthRecoversExactlyAt_prePayment_chain n a (orbitExactDepth n a)
      hdepth hexact with ⟨hchain, _⟩
  have hoff : t - a < orbitExactDepth n a - 1 := by
    unfold floatDebtPaymentTarget at htarget
    dsimp [a] at hstart htj htarget ⊢
    omega
  have hheight := (hchain (t - a) hoff).2
  simpa [show a + (t - a) = t by omega] using hheight

/-- The endpoint of a nonempty canonical block has an extra-height payment. -/
theorem two_le_orbitWindowHeight_floatPaymentBlock_endpoint
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    2 ≤ orbitWindowHeight n j := by
  let a := floatPaymentBlockStart n j h
  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
  have htarget : floatDebtPaymentTarget n a = j :=
    floatPaymentBlockStart_target_eq n j h
  have hpay := floatDebtAt_paymentTarget hdebt
  unfold PetalPaymentAt at hpay
  rwa [htarget] at hpay

/-- Every interior point of a canonical block has the same first-payment target. -/
theorem floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior
    {n : OddNat} {j t : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
    (ht : t ∈ floatPaymentBlockInterior n j h) :
    floatDebtPaymentTarget n t = j := by
  rcases Finset.mem_Ico.mp ht with ⟨hstart, htj⟩
  let a := floatPaymentBlockStart n j h
  have ha := floatPaymentBlockStart_mem_growthDebtFiber n j h
  have hdebt : FloatDebtAt n a := (mem_floatGrowthDebtFiberAt_iff.mp ha).2.1
  have htarget : floatDebtPaymentTarget n a = j :=
    floatPaymentBlockStart_target_eq n j h
  have hdepth := two_le_orbitExactDepth_of_floatDebtAt hdebt
  have hexact : OrbitDepthRecoversExactlyAt n a (orbitExactDepth n a) := by rfl
  rcases orbitDepthRecoversExactlyAt_prePayment_chain n a (orbitExactDepth n a)
      hdepth hexact with ⟨hchain, _⟩
  have hoff : t - a < orbitExactDepth n a - 1 := by
    unfold floatDebtPaymentTarget at htarget
    dsimp [a] at hstart htj htarget ⊢
    omega
  have hrec := (hchain (t - a) hoff).1
  have hdeptht : orbitExactDepth n t = orbitExactDepth n a - (t - a) := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
      show a + (t - a) = t by omega] using hrec
  unfold floatDebtPaymentTarget at htarget ⊢
  dsimp [a] at hstart htj htarget hdeptht ⊢
  omega

/-- Every delayed debt with target `j` lies in the canonical interior block. -/
theorem mem_floatPaymentBlockInterior_of_mem_growthDebtFiber
    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
    (hi : i ∈ floatGrowthDebtFiberAt n j) :
    i ∈ floatPaymentBlockInterior n j h := by
  apply Finset.mem_Ico.mpr
  constructor
  · exact Finset.min'_le _ _ hi
  · exact lt_of_mem_floatGrowthDebtFiberAt hi

/-- Delayed debts targeting `j` are exactly carry-two positions in its full interior block. -/
theorem mem_growthDebtFiber_iff_mem_floatPaymentBlockInterior_and_carryTwo
    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty} :
    i ∈ floatGrowthDebtFiberAt n j ↔
      i ∈ floatPaymentBlockInterior n j h ∧ CarryTwoDebtAt n i := by
  constructor
  · intro hi
    refine ⟨mem_floatPaymentBlockInterior_of_mem_growthDebtFiber hi, ?_⟩
    have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hi).2.1
    exact ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt).1
  · rintro ⟨hblock, hcarry⟩
    have hheight := orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hblock
    have hdelayed : DelayedCarryTwoDebtAt n i := ⟨hcarry, hheight⟩
    have hdebt : FloatDebtAt n i :=
      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
    apply mem_floatGrowthDebtFiberAt_iff.mpr
    rcases Finset.mem_Ico.mp hblock with ⟨_, hij⟩
    exact ⟨Nat.lt_succ_of_lt hij, hdebt,
      floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior hblock⟩

/-- The delayed-growth fiber is the carry-two filter of the full height-one interior. -/
theorem floatGrowthDebtFiberAt_eq_filter_floatPaymentBlockInterior_carryTwo
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    floatGrowthDebtFiberAt n j =
      carryTwoPositions n (floatPaymentBlockInterior n j h) := by
  ext i
  rw [mem_carryTwoPositions_iff]
  exact mem_growthDebtFiber_iff_mem_floatPaymentBlockInterior_and_carryTwo

/-- A complete claim arriving at `j` is a carry-two position in the full block. -/
theorem mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
    {n : OddNat} {i j : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty} :
    i ∈ carryTwoPaymentClaimFiberAt n j ↔
      i ∈ floatPaymentBlockWithEndpoint n j h ∧ CarryTwoDebtAt n i := by
  constructor
  · intro hi
    have hclaim := (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2
    rcases hclaim with hdelayed | himmediate
    · rcases hdelayed with ⟨hdelayed, htarget⟩
      have hdebt : FloatDebtAt n i :=
        (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
      have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
        (mem_floatGrowthDebtFiberAt_iff.mpr
          ⟨by rw [htarget]; exact Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget hdebt),
            hdebt, htarget.symm⟩)
      exact ⟨Finset.mem_Icc.mpr
        ⟨Finset.min'_le _ _ hfiber, (lt_of_mem_floatGrowthDebtFiberAt hfiber).le⟩,
        hdelayed.1⟩
    · rcases himmediate with ⟨himmediate, hself⟩
      subst j
      exact ⟨Finset.mem_Icc.mpr
        ⟨(floatPaymentBlockStart_lt_endpoint n i h).le, le_rfl⟩, himmediate.1⟩
  · rintro ⟨hblock, hcarry⟩
    rcases Finset.mem_Icc.mp hblock with ⟨hstart, hij⟩
    rcases hij.eq_or_lt with heq | hij
    · subst i
      exact mem_carryTwoPaymentClaimFiberAt_of_claim
        (Or.inr ⟨⟨hcarry, two_le_orbitWindowHeight_floatPaymentBlock_endpoint n j h⟩, rfl⟩)
    · have hinterior : i ∈ floatPaymentBlockInterior n j h :=
        Finset.mem_Ico.mpr ⟨hstart, hij⟩
      have hheight := orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hinterior
      have htarget :=
        floatDebtPaymentTarget_eq_endpoint_of_mem_floatPaymentBlockInterior hinterior
      exact mem_carryTwoPaymentClaimFiberAt_of_claim
        (Or.inl ⟨⟨hcarry, hheight⟩, htarget.symm⟩)

/-- The complete claim fiber is exactly the carry-two filter of the full block. -/
theorem carryTwoPaymentClaimFiberAt_eq_filter_floatPaymentBlockWithEndpoint_carryTwo
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    carryTwoPaymentClaimFiberAt n j =
      carryTwoPositions n (floatPaymentBlockWithEndpoint n j h) := by
  ext i
  rw [mem_carryTwoPositions_iff]
  exact mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo

/-- Cardinality form of the complete claim-fiber/block-filter identification. -/
theorem carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    (carryTwoPaymentClaimFiberAt n j).card =
      (carryTwoPositions n (floatPaymentBlockWithEndpoint n j h)).card := by
  exact congrArg Finset.card
    (carryTwoPaymentClaimFiberAt_eq_filter_floatPaymentBlockWithEndpoint_carryTwo n j h)

/-- Applying `T` commutes with a finite accelerated orbit prefix. -/
theorem T_iterateT_eq_iterateT_T
    (n : OddNat) (k : ℕ) :
    T (iterateT k n) = iterateT k (T n) := by
  rw [← iterateT_succ_eq_T_iterateT n k]
  rfl

/-- Iteration over a shifted orbit starts from the corresponding accelerated state. -/
theorem iterateT_add_eq_iterateT_from_shift
    (n : OddNat) (a len : ℕ) :
    iterateT (a + len) n = iterateT len (iterateT a n) := by
  induction a generalizing n with
  | zero => simp [iterateT]
  | succ a ih =>
      calc
        iterateT (a + 1 + len) n = T (iterateT (a + len) n) := by
          rw [show a + 1 + len = a + len + 1 by omega,
            iterateT_succ_eq_T_iterateT]
        _ = T (iterateT len (iterateT a n)) := by rw [ih]
        _ = iterateT len (T (iterateT a n)) := T_iterateT_eq_iterateT_T _ _
        _ = iterateT len (iterateT (a + 1) n) := by
          rw [iterateT_succ_eq_T_iterateT]

/-- Observation height in a shifted orbit is the global height at the shifted index. -/
theorem orbitWindowHeight_shift_eq
    (n : OddNat) (a t : ℕ) :
    orbitWindowHeight (iterateT a n) t = orbitWindowHeight n (a + t) := by
  rw [orbitWindowHeight_eq_s_iterateT, orbitWindowHeight_eq_s_iterateT,
    ← iterateT_add_eq_iterateT_from_shift]

/-- Total extra-height capacity over an explicit finite source set. -/
noncomputable def extraPaymentCapacityOn (n : OddNat) (S : Finset ℕ) : ℕ :=
  S.sum fun i => orbitWindowHeight n i - 1

/-- Endpoint arithmetic for a nonempty debt-supported payment block. -/
theorem floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h) = j + 1 := by
  have hlt := floatPaymentBlockStart_lt_endpoint n j h
  omega

/-- The shifted block interval is exactly the endpoint-inclusive canonical block. -/
theorem floatPaymentBlock_Ico_eq_withEndpoint
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    Finset.Ico (floatPaymentBlockStart n j h)
      (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h)) =
      floatPaymentBlockWithEndpoint n j h := by
  rw [floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ]
  unfold floatPaymentBlockWithEndpoint
  ext i
  simp

/-- Carry-two count on the half-open orbit segment `[a, a + len)`. -/
noncomputable def shiftedOrbitCarryTwoCount
    (n : OddNat) (a len : ℕ) : ℕ :=
  orbitWindowUpperCarryCountEqTwo (iterateT a n) len

/-- Extra-height capacity on the half-open orbit segment `[a, a + len)`. -/
noncomputable def shiftedExtraPaymentCapacity
    (n : OddNat) (a len : ℕ) : ℕ :=
  sumExtraHeight (iterateT a n) len

/-- Local offsets of carry-two sources in the shifted segment `[a, a + len)`. -/
noncomputable def shiftedCarryTwoOffsets
    (n : OddNat) (a len : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range len).filter fun t => CarryTwoDebtAt n (a + t)

/-- The recursive shifted carry-two count is the card of its local offset set. -/
theorem shiftedOrbitCarryTwoCount_eq_offset_card
    (n : OddNat) (a len : ℕ) :
    shiftedOrbitCarryTwoCount n a len = (shiftedCarryTwoOffsets n a len).card := by
  classical
  induction len with
  | zero =>
      simp [shiftedOrbitCarryTwoCount, shiftedCarryTwoOffsets,
        orbitWindowUpperCarryCountEqTwo]
  | succ len ih =>
      change orbitWindowUpperCarryCountEqTwo (iterateT a n) (len + 1) =
        ((Finset.range (len + 1)).filter fun t => CarryTwoDebtAt n (a + t)).card
      rw [orbitWindowUpperCarryCountEqTwo]
      change shiftedOrbitCarryTwoCount n a len +
          (if stateUpperCarry (iterateT len (iterateT a n)).1 = 2 then 1 else 0) = _
      rw [ih, Finset.range_add_one]
      change ((Finset.range len).filter fun t => CarryTwoDebtAt n (a + t)).card +
          (if stateUpperCarry (iterateT len (iterateT a n)).1 = 2 then 1 else 0) =
        ((insert len (Finset.range len)).filter fun t => CarryTwoDebtAt n (a + t)).card
      by_cases hcarry : CarryTwoDebtAt n (a + len)
      · have hstate : stateUpperCarry (iterateT len (iterateT a n)).1 = 2 := by
          simpa [CarryTwoDebtAt, ← iterateT_add_eq_iterateT_from_shift] using hcarry
        rw [Finset.filter_insert]
        simp [hcarry, hstate]
      · have hstate : stateUpperCarry (iterateT len (iterateT a n)).1 ≠ 2 := by
          simpa [CarryTwoDebtAt, ← iterateT_add_eq_iterateT_from_shift] using hcarry
        rw [Finset.filter_insert]
        simp [hcarry, hstate]

/-- Shifted extra-height capacity is the finite sum over local offsets. -/
theorem shiftedExtraPaymentCapacity_eq_sum_range
    (n : OddNat) (a len : ℕ) :
    shiftedExtraPaymentCapacity n a len =
      (Finset.range len).sum fun t => orbitWindowHeight n (a + t) - 1 := by
  induction len with
  | zero => simp [shiftedExtraPaymentCapacity, sumExtraHeight]
  | succ len ih =>
      change sumExtraHeight (iterateT a n) (len + 1) =
        (Finset.range (len + 1)).sum fun t => orbitWindowHeight n (a + t) - 1
      rw [sumExtraHeight]
      change shiftedExtraPaymentCapacity n a len +
          (s (iterateT len (iterateT a n)) - 1) = _
      rw [ih, Finset.sum_range_succ]
      have hheight : s (iterateT len (iterateT a n)) =
          orbitWindowHeight n (a + len) := by
        calc
          s (iterateT len (iterateT a n)) = s (iterateT (a + len) n) := by
            rw [iterateT_add_eq_iterateT_from_shift]
          _ = orbitWindowHeight n (a + len) :=
            (orbitWindowHeight_eq_s_iterateT n (a + len)).symm
      rw [hheight]

/-- Membership in the local carry-two offset set. -/
theorem mem_shiftedCarryTwoOffsets_iff
    {n : OddNat} {a len t : ℕ} :
    t ∈ shiftedCarryTwoOffsets n a len ↔ t < len ∧ CarryTwoDebtAt n (a + t) := by
  classical
  simp [shiftedCarryTwoOffsets]

/--
The global positions represented by local carry-two offsets.

The map is deliberately stated through `Finset.map`: its injectivity proof
makes the finite transport and its cardinal preservation explicit.
-/
noncomputable def shiftedCarryTwoPositions
    (n : OddNat) (a len : ℕ) : Finset ℕ := by
  classical
  exact (shiftedCarryTwoOffsets n a len).map
    ⟨fun t => a + t, by
      intro x y hxy
      exact Nat.add_left_cancel hxy⟩

/-- Local carry-two offsets are exactly the carry-two positions of the shifted interval. -/
theorem shiftedCarryTwoPositions_eq_carryTwoPositions_Ico
    (n : OddNat) (a len : ℕ) :
    shiftedCarryTwoPositions n a len =
      carryTwoPositions n (Finset.Ico a (a + len)) := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨t, ht, hti⟩
    rw [mem_carryTwoPositions_iff]
    rcases mem_shiftedCarryTwoOffsets_iff.mp ht with ⟨htlen, htcarry⟩
    rw [← hti]
    change a + t ∈ Finset.Ico a (a + len) ∧ CarryTwoDebtAt n (a + t)
    exact ⟨Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, htcarry⟩
  · intro hi
    rw [mem_carryTwoPositions_iff] at hi
    rcases hi with ⟨hiIco, hcarry⟩
    rcases Finset.mem_Ico.mp hiIco with ⟨hai, hiend⟩
    apply Finset.mem_map.mpr
    refine ⟨i - a, ?_, ?_⟩
    · apply mem_shiftedCarryTwoOffsets_iff.mpr
      constructor
      · omega
      · simpa [Nat.add_sub_of_le hai] using hcarry
    · exact Nat.add_sub_of_le hai

/-- Cardinality is preserved when local carry-two offsets are shifted globally. -/
theorem shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card
    (n : OddNat) (a len : ℕ) :
    (shiftedCarryTwoOffsets n a len).card =
      (carryTwoPositions n (Finset.Ico a (a + len))).card := by
  calc
    (shiftedCarryTwoOffsets n a len).card = (shiftedCarryTwoPositions n a len).card := by
      simp [shiftedCarryTwoPositions]
    _ = (carryTwoPositions n (Finset.Ico a (a + len))).card :=
      congrArg Finset.card (shiftedCarryTwoPositions_eq_carryTwoPositions_Ico n a len)

/--
On a canonical block, the shifted carry-two count is exactly the complete
first-payment claim-fiber cardinality at its endpoint.
-/
theorem shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    shiftedOrbitCarryTwoCount n (floatPaymentBlockStart n j h)
      (j + 1 - floatPaymentBlockStart n j h) =
      (carryTwoPaymentClaimFiberAt n j).card := by
  let a := floatPaymentBlockStart n j h
  let len := j + 1 - a
  calc
    shiftedOrbitCarryTwoCount n a len = (shiftedCarryTwoOffsets n a len).card :=
      shiftedOrbitCarryTwoCount_eq_offset_card n a len
    _ = (carryTwoPositions n (Finset.Ico a (a + len))).card :=
      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card n a len
    _ = (carryTwoPositions n (floatPaymentBlockWithEndpoint n j h)).card := by
      rw [floatPaymentBlock_Ico_eq_withEndpoint]
    _ = (carryTwoPaymentClaimFiberAt n j).card :=
      (carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card n j h).symm

/--
All extra-height capacity in a canonical block is concentrated at its endpoint.

Every earlier point is in the height-one interior, hence contributes zero to
`orbitWindowHeight - 1`.
-/
theorem extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    extraPaymentCapacityOn n (floatPaymentBlockWithEndpoint n j h) =
      orbitWindowHeight n j - 1 := by
  classical
  unfold extraPaymentCapacityOn
  apply Finset.sum_eq_single j
  · intro i hi hij
    have hii := Finset.mem_Icc.mp hi
    have hijlt : i < j := lt_of_le_of_ne hii.2 hij
    have hinterior : i ∈ floatPaymentBlockInterior n j h :=
      Finset.mem_Ico.mpr ⟨hii.1, hijlt⟩
    rw [orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior hinterior]
    rfl
  · intro hj
    exact False.elim (hj (Finset.mem_Icc.mpr
      ⟨(floatPaymentBlockStart_lt_endpoint n j h).le, le_rfl⟩))

/-- The shifted local extra-height sum is the capacity of its global half-open interval. -/
theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico
    (n : OddNat) (a len : ℕ) :
    shiftedExtraPaymentCapacity n a len =
      extraPaymentCapacityOn n (Finset.Ico a (a + len)) := by
  unfold extraPaymentCapacityOn
  rw [shiftedExtraPaymentCapacity_eq_sum_range]
  symm
  rw [Finset.sum_Ico_eq_sum_range]
  simp

/-- The shifted extra-height capacity of a canonical block is its endpoint capacity. -/
theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
      (j + 1 - floatPaymentBlockStart n j h) = extraPaymentCapacityAt n j := by
  calc
    shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
        (j + 1 - floatPaymentBlockStart n j h) =
        extraPaymentCapacityOn n (Finset.Ico (floatPaymentBlockStart n j h)
          (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h))) :=
      shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico n
        (floatPaymentBlockStart n j h) (j + 1 - floatPaymentBlockStart n j h)
    _ = extraPaymentCapacityOn n (floatPaymentBlockWithEndpoint n j h) := by
      rw [floatPaymentBlock_Ico_eq_withEndpoint]
    _ = orbitWindowHeight n j - 1 :=
      extraPaymentCapacityOn_floatPaymentBlockWithEndpoint_eq_endpoint_extra n j h
    _ = extraPaymentCapacityAt n j := rfl

/--
Exact width ledger on a canonical first-payment block.

The right side counts complete carry-two claims; the left side records the
single endpoint's available extra-height capacity.
-/
theorem bitWidth_iterateT_paymentBlock_eq_claimFiber_card
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    bitWidth (iterateT (j + 1) n).1 + extraPaymentCapacityAt n j =
      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
        (carryTwoPaymentClaimFiberAt n j).card := by
  have hledger :
      bitWidth (iterateT
        (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h)) n).1 +
          shiftedExtraPaymentCapacity n (floatPaymentBlockStart n j h)
            (j + 1 - floatPaymentBlockStart n j h) =
        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 +
          shiftedOrbitCarryTwoCount n (floatPaymentBlockStart n j h)
            (j + 1 - floatPaymentBlockStart n j h) := by
    unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
    rw [iterateT_add_eq_iterateT_from_shift]
    exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
      (iterateT (floatPaymentBlockStart n j h) n)
      (j + 1 - floatPaymentBlockStart n j h)
  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt,
    shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card] at hledger
  simpa [floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ] using hledger

/-- A canonical block overload is exactly a strict width increase across the block. -/
theorem carryTwoPaymentOverloadAt_iff_bitWidth_paymentBlock_lt
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    CarryTwoPaymentOverloadAt n j ↔
      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 <
        bitWidth (iterateT (j + 1) n).1 := by
  unfold CarryTwoPaymentOverloadAt
  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
  omega

/-- Claim capacity is balanced exactly when the canonical block preserves width. -/
theorem carryTwoPaymentClaimFiber_card_eq_capacity_iff_bitWidth_paymentBlock_eq
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    (carryTwoPaymentClaimFiberAt n j).card = extraPaymentCapacityAt n j ↔
      bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 =
        bitWidth (iterateT (j + 1) n).1 := by
  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
  omega

/-- Claim capacity is surplus exactly when the canonical block strictly decreases width. -/
theorem carryTwoPaymentClaimFiber_card_lt_capacity_iff_bitWidth_paymentBlock_gt
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    (carryTwoPaymentClaimFiberAt n j).card < extraPaymentCapacityAt n j ↔
      bitWidth (iterateT (j + 1) n).1 <
        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 := by
  have hledger := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
  omega

/--
Exact shifted width ledger.

This is the existing prefix ledger, based at `iterateT a n`; no new induction
over a segment is required.
-/
theorem bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
    (n : OddNat) (a len : ℕ) :
    bitWidth (iterateT (a + len) n).1 + shiftedExtraPaymentCapacity n a len =
      bitWidth (iterateT a n).1 + shiftedOrbitCarryTwoCount n a len := by
  unfold shiftedExtraPaymentCapacity shiftedOrbitCarryTwoCount
  rw [iterateT_add_eq_iterateT_from_shift]
  exact bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
    (iterateT a n) len

/-!
## Ledger frontier

The local-offset transport is now complete.  On a nonempty canonical block,
the shifted carry-two count is the complete claim-fiber cardinality and the
shifted extra-height sum is the endpoint capacity.  Their exact ledger gives a
three-way arithmetic classification: overload, equality, and surplus are
respectively strict width growth, width preservation, and strict width decay.

This remains a block-local accounting theorem.  It does not allocate claims to
individual height units, assert coverage of arbitrary orbit intervals, or
derive an ambient pressure conclusion without further hypotheses.
-/

end DkMath.Collatz
