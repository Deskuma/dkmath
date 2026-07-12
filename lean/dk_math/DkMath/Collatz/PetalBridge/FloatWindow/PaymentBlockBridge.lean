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

/-- Carry-two count on the half-open orbit segment `[a, a + len)`. -/
noncomputable def shiftedOrbitCarryTwoCount
    (n : OddNat) (a len : ℕ) : ℕ :=
  orbitWindowUpperCarryCountEqTwo (iterateT a n) len

/-- Extra-height capacity on the half-open orbit segment `[a, a + len)`. -/
noncomputable def shiftedExtraPaymentCapacity
    (n : OddNat) (a len : ℕ) : ℕ :=
  sumExtraHeight (iterateT a n) len

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

The block and its complete first-claim fiber are now canonical, and the
existing prefix ledger has been repackaged as a shifted segment ledger.
To obtain the proposed endpoint-only block identity, the remaining task is a
reindexing theorem: identify the shifted carry count on `[a, j + 1)` with the
canonical claim fiber, and identify its shifted extra-height sum with the
single endpoint capacity.  The latter needs a finite-sum transport lemma from
the interior height-one theorem.  No claim allocation or ambient pressure
conclusion is inferred before those two exact identifications are proved.
-/

end DkMath.Collatz
