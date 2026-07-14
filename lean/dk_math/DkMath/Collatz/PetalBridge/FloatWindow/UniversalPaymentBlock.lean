/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock"

namespace DkMath.Collatz

set_option linter.style.longLine false

/-!
# Universal first-payment coordinates

The earlier `floatDebtPaymentTarget` was introduced for delayed width-growth
debts.  Exact all-ones depth, however, assigns the same canonical target to
every orbit time.  This module exposes that total coordinate without turning a
first-claim relation into a final allocation claim.
-/

/-- The canonical payment target determined by exact all-ones depth at any orbit time. -/
noncomputable def orbitPaymentTarget (n : OddNat) (i : ℕ) : ℕ :=
  i + orbitExactDepth n i - 1

/-- The debt-facing target is definitionally the universal target. -/
theorem floatDebtPaymentTarget_eq_orbitPaymentTarget
    (n : OddNat) (i : ℕ) :
    floatDebtPaymentTarget n i = orbitPaymentTarget n i := rfl

/-- A height-one source has a strictly later canonical payment target. -/
theorem lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one
    {n : OddNat} {i : ℕ}
    (hheight : orbitWindowHeight n i = 1) :
    i < orbitPaymentTarget n i := by
  unfold orbitPaymentTarget
  have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
  omega

/-- An extra-height event pays immediately at its own orbit time. -/
theorem orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
    {n : OddNat} {i : ℕ}
    (hheight : 2 ≤ orbitWindowHeight n i) :
    orbitPaymentTarget n i = i := by
  unfold orbitPaymentTarget
  have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 hheight
  omega

/-- Every canonical payment target is at or after its source time. -/
theorem le_orbitPaymentTarget
    (n : OddNat) (i : ℕ) :
    i ≤ orbitPaymentTarget n i := by
  by_cases hheight : orbitWindowHeight n i = 1
  · exact (lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hheight).le
  · have htwo : 2 ≤ orbitWindowHeight n i := by
      have hone := orbitWindowHeight_one_le n i
      omega
    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]

/-- A time is a target fixed point exactly when it is an extra-height event. -/
theorem orbitPaymentTarget_eq_self_iff_two_le_orbitWindowHeight
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n i = i ↔ 2 ≤ orbitWindowHeight n i := by
  constructor
  · intro htarget
    by_contra hnot
    have hone : orbitWindowHeight n i = 1 := by
      have hpos := orbitWindowHeight_one_le n i
      omega
    have hlt := lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hone
    omega
  · exact orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight

/-- A height-one step preserves its eventual canonical payment target. -/
theorem orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one
    {n : OddNat} {i : ℕ}
    (hheight : orbitWindowHeight n i = 1) :
    orbitPaymentTarget n (i + 1) = orbitPaymentTarget n i := by
  have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
  have hexact : OrbitDepthRecoversExactlyAt n i (orbitExactDepth n i) := by rfl
  by_cases hd2 : orbitExactDepth n i = 2
  · have hnext : 2 ≤ orbitWindowHeight n (i + 1) := by
      simpa [hd2] using
        orbitDepthRecoversExactlyAt_delayed_height_two_le n i (orbitExactDepth n i)
          hdepth hexact
    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hnext]
    unfold orbitPaymentTarget
    omega
  · have hd3 : 3 ≤ orbitExactDepth n i := by omega
    have hnextExact := orbitDepthRecoversExactlyAt_succ_of_three_le
      n i (orbitExactDepth n i) hd3 hexact
    have hnextDepth : orbitExactDepth n (i + 1) = orbitExactDepth n i - 1 := by
      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hnextExact
    unfold orbitPaymentTarget
    omega

/-- An extra-height step moves strictly to a later canonical payment target. -/
theorem orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
    {n : OddNat} {i : ℕ}
    (hheight : 2 ≤ orbitWindowHeight n i) :
    orbitPaymentTarget n i < orbitPaymentTarget n (i + 1) := by
  rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight]
  have hle := le_orbitPaymentTarget n (i + 1)
  omega

/-- Every orbit time targets a genuine extra-height payment slot. -/
theorem two_le_orbitWindowHeight_orbitPaymentTarget
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n (orbitPaymentTarget n i) := by
  by_cases hheight : orbitWindowHeight n i = 1
  · have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
    have hexact : OrbitDepthRecoversExactlyAt n i (orbitExactDepth n i) := by rfl
    simpa [orbitPaymentTarget] using
      orbitDepthRecoversExactlyAt_delayed_height_two_le n i (orbitExactDepth n i) hdepth hexact
  · have htwo : 2 ≤ orbitWindowHeight n i := by
      have hone := orbitWindowHeight_one_le n i
      omega
    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
    exact htwo

/-- Canonical payment targets are fixed points of the target map. -/
theorem orbitPaymentTarget_target
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n (orbitPaymentTarget n i) = orbitPaymentTarget n i := by
  apply orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
  exact two_le_orbitWindowHeight_orbitPaymentTarget n i

/-- All sources at most `j` whose canonical payment target is `j`. -/
noncomputable def orbitPaymentSourceFiberAt (n : OddNat) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (j + 1)).filter fun i => orbitPaymentTarget n i = j

/-- Membership API for a universal canonical payment-source fiber. -/
theorem mem_orbitPaymentSourceFiberAt_iff
    {n : OddNat} {i j : ℕ} :
    i ∈ orbitPaymentSourceFiberAt n j ↔ i ≤ j ∧ orbitPaymentTarget n i = j := by
  classical
  simp [orbitPaymentSourceFiberAt]

/-- A nonempty universal source fiber has a canonical earliest source. -/
noncomputable def universalPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) : ℕ :=
  (orbitPaymentSourceFiberAt n j).min' h

/-- The universal block start belongs to its endpoint's source fiber. -/
theorem universalPaymentBlockStart_mem_sourceFiber
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockStart n j h ∈ orbitPaymentSourceFiberAt n j :=
  Finset.min'_mem _ h

/-- Every time belongs to the universal source fiber of its own canonical target. -/
theorem self_mem_orbitPaymentSourceFiberAt_target
    (n : OddNat) (i : ℕ) :
    i ∈ orbitPaymentSourceFiberAt n (orbitPaymentTarget n i) := by
  rw [mem_orbitPaymentSourceFiberAt_iff]
  constructor
  · by_cases hheight : orbitWindowHeight n i = 1
    · exact (lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hheight).le
    · have htwo : 2 ≤ orbitWindowHeight n i := by
        have hone := orbitWindowHeight_one_le n i
        omega
      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
  · rfl

/-- Every canonical payment target has a nonempty universal source fiber. -/
theorem orbitPaymentSourceFiberAt_nonempty_target
    (n : OddNat) (i : ℕ) :
    (orbitPaymentSourceFiberAt n (orbitPaymentTarget n i)).Nonempty :=
  ⟨i, self_mem_orbitPaymentSourceFiberAt_target n i⟩

/-- A nonempty universal source fiber has an actual extra-height endpoint. -/
theorem two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty
    {n : OddNat} {j : ℕ}
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    2 ≤ orbitWindowHeight n j := by
  rcases h with ⟨i, hi⟩
  have htarget := (mem_orbitPaymentSourceFiberAt_iff.mp hi).2
  rw [← htarget]
  exact two_le_orbitWindowHeight_orbitPaymentTarget n i

/-- A nonempty universal source fiber contains its endpoint as the immediate source. -/
theorem endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
    {n : OddNat} {j : ℕ}
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    j ∈ orbitPaymentSourceFiberAt n j := by
  rw [mem_orbitPaymentSourceFiberAt_iff]
  exact ⟨le_rfl,
    orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
      (two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h)⟩

/-- Every delayed growth-debt source is a universal source for the same target. -/
theorem mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
    {n : OddNat} {i j : ℕ}
    (hi : i ∈ floatGrowthDebtFiberAt n j) :
    i ∈ orbitPaymentSourceFiberAt n j := by
  rcases mem_floatGrowthDebtFiberAt_iff.mp hi with ⟨hij, _, htarget⟩
  rw [mem_orbitPaymentSourceFiberAt_iff]
  exact ⟨by omega,
    by simpa [← floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget⟩

/-- A nonempty delayed growth-debt fiber induces a nonempty universal source fiber. -/
theorem orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty
    {n : OddNat} {j : ℕ}
    (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    (orbitPaymentSourceFiberAt n j).Nonempty := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi⟩

/--
The universal block begins no later than the delayed-growth-debt block.

This is only an inclusion-of-fibers statement.  Equality is not claimed: the
universal fiber can contain height-one sources that are not Float growth debts.
-/
theorem universalPaymentBlockStart_le_floatPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    universalPaymentBlockStart n j
      (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h) ≤
      floatPaymentBlockStart n j h := by
  apply Finset.min'_le
  exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
    (floatPaymentBlockStart_mem_growthDebtFiber n j h)

/--
Every strict interior point after a universal block start has the endpoint as
its canonical payment target.
-/
theorem orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt
    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
    (hstart : universalPaymentBlockStart n j h ≤ i) (hij : i < j) :
    orbitPaymentTarget n i = j := by
  let b := universalPaymentBlockStart n j h
  have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
  have hbtarget : orbitPaymentTarget n b = j :=
    (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
  have hbj : b < j := lt_of_le_of_lt hstart hij
  have hdepth : 2 ≤ orbitExactDepth n b := by
    unfold orbitPaymentTarget at hbtarget
    omega
  have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
  rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
      hdepth hexact with ⟨hchain, _⟩
  have hoff : i - b < orbitExactDepth n b - 1 := by
    unfold orbitPaymentTarget at hbtarget
    dsimp [b] at hstart hbj hbtarget ⊢
    omega
  have hiExact := (hchain (i - b) hoff).1
  have hdepthi : orbitExactDepth n i = orbitExactDepth n b - (i - b) := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
      show b + (i - b) = i by omega] using hiExact
  unfold orbitPaymentTarget at hbtarget ⊢
  dsimp [b] at hstart hbj hdepthi hbtarget ⊢
  omega

/-- A nonempty universal source fiber is exactly its minimum-to-endpoint interval. -/
theorem orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    orbitPaymentSourceFiberAt n j =
      Finset.Icc (universalPaymentBlockStart n j h) j := by
  ext i
  constructor
  · intro hi
    rcases mem_orbitPaymentSourceFiberAt_iff.mp hi with ⟨hij, _⟩
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hi, hij⟩
  · intro hi
    rcases Finset.mem_Icc.mp hi with ⟨hstart, hij⟩
    rw [mem_orbitPaymentSourceFiberAt_iff]
    constructor
    · exact hij
    · rcases hij.eq_or_lt with rfl | hijlt
      · exact orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
          (two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h)
      · exact orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hijlt

/-- Strict universal-block interior points have exact observed height one. -/
theorem orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
    (hi : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j) :
    orbitWindowHeight n i = 1 := by
  rcases Finset.mem_Ico.mp hi with ⟨hstart, hij⟩
  let b := universalPaymentBlockStart n j h
  have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
  have hbtarget : orbitPaymentTarget n b = j :=
    (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
  have hdepth : 2 ≤ orbitExactDepth n b := by
    unfold orbitPaymentTarget at hbtarget
    dsimp [b] at hstart hij hbtarget ⊢
    omega
  have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
  rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
      hdepth hexact with ⟨hchain, _⟩
  have hoff : i - b < orbitExactDepth n b - 1 := by
    unfold orbitPaymentTarget at hbtarget
    dsimp [b] at hstart hij hbtarget ⊢
    omega
  simpa [show b + (i - b) = i by omega] using (hchain (i - b) hoff).2

/-- The exact-depth profile on a universal payment block is the descending staircase to one. -/
theorem orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
    (hi : i ∈ Finset.Icc (universalPaymentBlockStart n j h) j) :
    orbitExactDepth n i = j - i + 1 := by
  rcases Finset.mem_Icc.mp hi with ⟨hstart, hij⟩
  rcases hij.eq_or_lt with rfl | hijlt
  · have htwo := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
    have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 htwo
    omega
  · let b := universalPaymentBlockStart n j h
    have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
    have hbtarget : orbitPaymentTarget n b = j :=
      (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
    have hdepth : 2 ≤ orbitExactDepth n b := by
      unfold orbitPaymentTarget at hbtarget
      dsimp [b] at hstart hijlt hbtarget ⊢
      omega
    have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
    rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
        hdepth hexact with ⟨hchain, _⟩
    have hoff : i - b < orbitExactDepth n b - 1 := by
      unfold orbitPaymentTarget at hbtarget
      dsimp [b] at hstart hijlt hbtarget ⊢
      omega
    have hiExact := (hchain (i - b) hoff).1
    have hdepthi : orbitExactDepth n i = orbitExactDepth n b - (i - b) := by
      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
        show b + (i - b) = i by omega] using hiExact
    unfold orbitPaymentTarget at hbtarget
    dsimp [b] at hstart hijlt hbtarget hdepthi ⊢
    omega

/-- Canonical payment targets are nondecreasing across one orbit step. -/
theorem orbitPaymentTarget_le_succ
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n i ≤ orbitPaymentTarget n (i + 1) := by
  by_cases hheight : orbitWindowHeight n i = 1
  · rw [orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one hheight]
  · have htwo : 2 ≤ orbitWindowHeight n i := by
      have hone := orbitWindowHeight_one_le n i
      omega
    exact (orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight htwo).le

/-- The target map is monotone on natural orbit times. -/
theorem monotone_orbitPaymentTarget (n : OddNat) :
    Monotone (orbitPaymentTarget n) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (orbitPaymentTarget_le_succ n b)

/-- Equal successive targets occur exactly at height-one sources. -/
theorem orbitPaymentTarget_succ_eq_iff_orbitWindowHeight_eq_one
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n (i + 1) = orbitPaymentTarget n i ↔
      orbitWindowHeight n i = 1 := by
  constructor
  · intro heq
    by_contra hnot
    have htwo : 2 ≤ orbitWindowHeight n i := by
      have hone := orbitWindowHeight_one_le n i
      omega
    have hlt := orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight htwo
    omega
  · exact orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one

/-- Strict target advance occurs exactly at extra-height sources. -/
theorem orbitPaymentTarget_lt_succ_iff_two_le_orbitWindowHeight
    (n : OddNat) (i : ℕ) :
    orbitPaymentTarget n i < orbitPaymentTarget n (i + 1) ↔
      2 ≤ orbitWindowHeight n i := by
  constructor
  · intro hlt
    by_contra hnot
    have hone : orbitWindowHeight n i = 1 := by
      have hpos := orbitWindowHeight_one_le n i
      omega
    have heq := orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one hone
    omega
  · exact orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight

/-- Nonempty universal source fibers are exactly the extra-height endpoints. -/
theorem orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight
    (n : OddNat) (j : ℕ) :
    (orbitPaymentSourceFiberAt n j).Nonempty ↔ 2 ≤ orbitWindowHeight n j := by
  constructor
  · exact two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty
  · intro htwo
    refine ⟨j, ?_⟩
    rw [mem_orbitPaymentSourceFiberAt_iff]
    exact ⟨le_rfl, orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo⟩

/-- The finite bound in a universal source fiber is implied by target extensivity. -/
theorem mem_orbitPaymentSourceFiberAt_iff_target_eq
    {n : OddNat} {i j : ℕ} :
    i ∈ orbitPaymentSourceFiberAt n j ↔ orbitPaymentTarget n i = j := by
  constructor
  · intro hi
    exact (mem_orbitPaymentSourceFiberAt_iff.mp hi).2
  · intro htarget
    rw [mem_orbitPaymentSourceFiberAt_iff]
    exact ⟨by rw [← htarget]; exact le_orbitPaymentTarget n i, htarget⟩

/--
The complete carry-two claim fiber at a universal endpoint is its carry-two
filter on the full universal payment block.
-/
theorem mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
    i ∈ carryTwoPaymentClaimFiberAt n j ↔
      i ∈ Finset.Icc (universalPaymentBlockStart n j h) j ∧ CarryTwoDebtAt n i := by
  constructor
  · intro hi
    rcases (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2 with hdelayed | himmediate
    · rcases hdelayed with ⟨⟨hcarry, hheight⟩, htarget⟩
      have htarget' : orbitPaymentTarget n i = j := by
        simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget.symm
      have hfiber := mem_orbitPaymentSourceFiberAt_iff_target_eq.mpr htarget'
      have hblock : i ∈ Finset.Icc (universalPaymentBlockStart n j h) j := by
        rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
        exact hfiber
      exact ⟨hblock, hcarry⟩
    · rcases himmediate with ⟨⟨hcarry, _⟩, hself⟩
      subst j
      have hstartmem := universalPaymentBlockStart_mem_sourceFiber n i h
      exact ⟨Finset.mem_Icc.mpr
        ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1,
          le_rfl⟩, hcarry⟩
  · rintro ⟨hblock, hcarry⟩
    rcases Finset.mem_Icc.mp hblock with ⟨hstart, hij⟩
    apply mem_carryTwoPaymentClaimFiberAt_of_claim
    rcases hij.eq_or_lt with rfl | hijlt
    · right
      exact ⟨⟨hcarry,
        two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h⟩, rfl⟩
    · left
      have hheight : orbitWindowHeight n i = 1 :=
        orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
          (Finset.mem_Ico.mpr ⟨hstart, hijlt⟩)
      have htarget : orbitPaymentTarget n i = j :=
        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hijlt
      exact ⟨⟨hcarry, hheight⟩,
        by simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget.symm⟩

/-- Finset form of the universal complete-claim/block-filter identification. -/
theorem carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    carryTwoPaymentClaimFiberAt n j =
      carryTwoPositions n (Finset.Icc (universalPaymentBlockStart n j h) j) := by
  ext i
  rw [mem_carryTwoPositions_iff]
  exact mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo

/-- Cardinality form of the universal complete-claim/block-filter identification. -/
theorem carryTwoPaymentClaimFiberAt_card_eq_universalPaymentBlock_carryTwo_card
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    (carryTwoPaymentClaimFiberAt n j).card =
      (carryTwoPositions n (Finset.Icc (universalPaymentBlockStart n j h) j)).card :=
  congrArg Finset.card
    (carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n j h)

/-- All extra-height capacity in a universal payment block is concentrated at its endpoint. -/
theorem extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    extraPaymentCapacityOn n (Finset.Icc (universalPaymentBlockStart n j h) j) =
      extraPaymentCapacityAt n j := by
  unfold extraPaymentCapacityOn extraPaymentCapacityAt
  apply Finset.sum_eq_single j
  · intro i hi hij
    rcases Finset.mem_Icc.mp hi with ⟨hstart, hijle⟩
    have hijlt : i < j := lt_of_le_of_ne hijle hij
    have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
      (Finset.mem_Ico.mpr ⟨hstart, hijlt⟩)
    rw [hheight]
    rfl
  · intro hj
    have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
    exact False.elim (hj (Finset.mem_Icc.mpr
      ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩))

/-- Endpoint arithmetic for a nonempty universal payment block. -/
theorem universalPaymentBlockStart_add_length_eq_endpoint_succ
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockStart n j h +
      (j + 1 - universalPaymentBlockStart n j h) = j + 1 := by
  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
  have hle := (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
  omega

/-- The shifted universal interval is exactly the endpoint-inclusive universal block. -/
theorem universalPaymentBlock_Ico_eq_Icc
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    Finset.Ico (universalPaymentBlockStart n j h)
      (universalPaymentBlockStart n j h +
        (j + 1 - universalPaymentBlockStart n j h)) =
      Finset.Icc (universalPaymentBlockStart n j h) j := by
  rw [universalPaymentBlockStart_add_length_eq_endpoint_succ]
  ext i
  simp

/-- Shifted carry-two count on a universal payment block is its complete claim count. -/
theorem shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card_universal
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    shiftedOrbitCarryTwoCount n (universalPaymentBlockStart n j h)
      (j + 1 - universalPaymentBlockStart n j h) =
      (carryTwoPaymentClaimFiberAt n j).card := by
  let b := universalPaymentBlockStart n j h
  let len := j + 1 - b
  calc
    shiftedOrbitCarryTwoCount n b len = (shiftedCarryTwoOffsets n b len).card :=
      shiftedOrbitCarryTwoCount_eq_offset_card n b len
    _ = (carryTwoPositions n (Finset.Ico b (b + len))).card :=
      shiftedCarryTwoOffsets_card_eq_carryTwoPositions_Ico_card n b len
    _ = (carryTwoPositions n (Finset.Icc b j)).card := by
      rw [universalPaymentBlock_Ico_eq_Icc]
    _ = (carryTwoPaymentClaimFiberAt n j).card :=
      (carryTwoPaymentClaimFiberAt_card_eq_universalPaymentBlock_carryTwo_card n j h).symm

/-- Shifted extra-height capacity on a universal block is its endpoint capacity. -/
theorem shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt_universal
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    shiftedExtraPaymentCapacity n (universalPaymentBlockStart n j h)
      (j + 1 - universalPaymentBlockStart n j h) = extraPaymentCapacityAt n j := by
  let b := universalPaymentBlockStart n j h
  let len := j + 1 - b
  calc
    shiftedExtraPaymentCapacity n b len =
        extraPaymentCapacityOn n (Finset.Ico b (b + len)) :=
      shiftedExtraPaymentCapacity_eq_extraPaymentCapacityOn_Ico n b len
    _ = extraPaymentCapacityOn n (Finset.Icc b j) := by
      rw [universalPaymentBlock_Ico_eq_Icc]
    _ = extraPaymentCapacityAt n j :=
      extraPaymentCapacityOn_universalPaymentBlock_eq_endpoint_capacity n j h

/-- Exact width ledger for every nonempty universal payment block. -/
theorem bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    bitWidth (iterateT (j + 1) n).1 + extraPaymentCapacityAt n j =
      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 +
        (carryTwoPaymentClaimFiberAt n j).card := by
  have hledger := bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
    n (universalPaymentBlockStart n j h) (j + 1 - universalPaymentBlockStart n j h)
  rw [shiftedExtraPaymentCapacity_eq_extraPaymentCapacityAt_universal,
    shiftedOrbitCarryTwoCount_eq_carryTwoPaymentClaimFiber_card_universal] at hledger
  simpa [universalPaymentBlockStart_add_length_eq_endpoint_succ] using hledger

/-- Proof-independent signed drift at a universal payment endpoint. -/
noncomputable def universalPaymentBlockSignedDriftAt (n : OddNat) (j : ℕ) : ℤ :=
  (carryTwoPaymentClaimFiberAt n j).card - extraPaymentCapacityAt n j

/-- Universal signed drift equals signed width drift across a nonempty block. -/
theorem universalPaymentBlockSignedDriftAt_eq_bitWidth_sub
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockSignedDriftAt n j =
      (bitWidth (iterateT (j + 1) n).1 : ℤ) -
        bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
  unfold universalPaymentBlockSignedDriftAt
  have hledger := bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card n j h
  omega

/-- Positive universal signed drift is exactly strict block-width growth. -/
theorem universalPaymentBlockSignedDriftAt_pos_iff_bitWidth_lt
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    0 < universalPaymentBlockSignedDriftAt n j ↔
      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 <
        bitWidth (iterateT (j + 1) n).1 := by
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
  omega

/-- Zero universal signed drift is exactly block-width preservation. -/
theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_bitWidth_eq
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockSignedDriftAt n j = 0 ↔
      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 =
        bitWidth (iterateT (j + 1) n).1 := by
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
  omega

/-- Negative universal signed drift is exactly strict block-width decay. -/
theorem universalPaymentBlockSignedDriftAt_neg_iff_bitWidth_gt
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockSignedDriftAt n j < 0 ↔
      bitWidth (iterateT (j + 1) n).1 <
        bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h]
  omega

/-- Positive universal signed drift is exactly claim-count overload over capacity. -/
theorem universalPaymentBlockSignedDriftAt_pos_iff_claim_card_lt
    (n : OddNat) (j : ℕ) :
    0 < universalPaymentBlockSignedDriftAt n j ↔
      extraPaymentCapacityAt n j < (carryTwoPaymentClaimFiberAt n j).card := by
  unfold universalPaymentBlockSignedDriftAt
  omega

/-- Zero universal signed drift is exactly claim/capacity balance. -/
theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity
    (n : OddNat) (j : ℕ) :
    universalPaymentBlockSignedDriftAt n j = 0 ↔
      (carryTwoPaymentClaimFiberAt n j).card = extraPaymentCapacityAt n j := by
  unfold universalPaymentBlockSignedDriftAt
  omega

/-- Negative universal signed drift is exactly strict endpoint-capacity surplus. -/
theorem universalPaymentBlockSignedDriftAt_neg_iff_claim_card_lt_capacity
    (n : OddNat) (j : ℕ) :
    universalPaymentBlockSignedDriftAt n j < 0 ↔
      (carryTwoPaymentClaimFiberAt n j).card < extraPaymentCapacityAt n j := by
  unfold universalPaymentBlockSignedDriftAt
  omega

/-!
## Blocks with no delayed growth debt

The following classification is deliberately local to one universal payment
block.  Empty delayed-debt support does not assert anything about later
blocks; it only excludes carry-two events at the height-one interior points of
this particular canonical target fiber.
-/

/--
In a debt-free universal block, every strict interior source has upper carry
one.  A carry of two together with the already-known height-one interior
profile would be a delayed growth debt for the same endpoint.
-/
theorem stateUpperCarry_eq_one_of_mem_universalPaymentBlockInterior_of_growthDebtFiber_eq_empty
    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
    (hempty : floatGrowthDebtFiberAt n j = ∅)
    (hi : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j) :
    stateUpperCarry (iterateT i n).1 = 1 := by
  have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior hi
  have hnotcarry : ¬ CarryTwoDebtAt n i := by
    intro hcarry
    have hdebt : FloatDebtAt n i :=
      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
    rcases Finset.mem_Ico.mp hi with ⟨hstart, hij⟩
    have htarget : floatDebtPaymentTarget n i = j := by
      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hij
    have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
      mem_floatGrowthDebtFiberAt_iff.mpr ⟨Nat.lt_succ_of_lt hij, hdebt, htarget⟩
    simp [hempty] at hfiber
  have hpos : 0 < (iterateT i n).1 := by
    have hodd := (iterateT i n).2
    omega
  rcases stateUpperCarry_one_or_two hpos with hone | htwo
  · exact hone
  · exact False.elim (hnotcarry htwo)

/--
With no delayed debt in a nonempty universal block, a complete carry-two claim
can occur only at the endpoint.  Thus the full claim fiber is either the
endpoint singleton or empty.
-/
theorem mem_carryTwoPaymentClaimFiberAt_iff_eq_endpoint_and_carryTwo_of_growthDebtFiber_eq_empty
    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    i ∈ carryTwoPaymentClaimFiberAt n j ↔ i = j ∧ CarryTwoDebtAt n j := by
  constructor
  · intro hi
    rcases mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo.mp hi with
      ⟨hblock, hcarry⟩
    have hijle := (Finset.mem_Icc.mp hblock).2
    by_cases hijEq : i = j
    · exact ⟨hijEq, by simpa [hijEq] using hcarry⟩
    · have hij : i < j := lt_of_le_of_ne hijle hijEq
      have hinterior : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j := by
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hblock).1, hij⟩
      have hone :=
        stateUpperCarry_eq_one_of_mem_universalPaymentBlockInterior_of_growthDebtFiber_eq_empty
          hempty hinterior
      exfalso
      unfold CarryTwoDebtAt at hcarry
      omega
  · rintro ⟨hi, hcarry⟩
    subst i
    apply
      mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := h) |>.mpr
    have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
    exact ⟨Finset.mem_Icc.mpr
      ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩, hcarry⟩

/-- The endpoint-only candidate shape for a debt-free universal claim fiber. -/
noncomputable def endpointCarryTwoClaimShape (n : OddNat) (j : ℕ) : Finset ℕ := by
  classical
  exact if CarryTwoDebtAt n j then {j} else ∅

/-- Finset form: debt-free universal blocks have at most their endpoint claim. -/
theorem carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    carryTwoPaymentClaimFiberAt n j = endpointCarryTwoClaimShape n j := by
  classical
  ext i
  unfold endpointCarryTwoClaimShape
  rw [mem_carryTwoPaymentClaimFiberAt_iff_eq_endpoint_and_carryTwo_of_growthDebtFiber_eq_empty
    (h := h) hempty]
  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]

/-- A debt-free universal block has at most one complete carry-two claim. -/
theorem carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    (carryTwoPaymentClaimFiberAt n j).card ≤ 1 := by
  rw [carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
    n j h hempty]
  unfold endpointCarryTwoClaimShape
  classical
  split <;> simp

/-- Every nonempty universal endpoint has at least one unit of payment capacity. -/
theorem one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty
    {n : OddNat} {j : ℕ}
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    1 ≤ extraPaymentCapacityAt n j := by
  unfold extraPaymentCapacityAt
  have hheight := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
  omega

/-- In a debt-free universal block, complete claims do not exceed endpoint capacity. -/
theorem carryTwoPaymentClaimFiberAt_card_le_extraPaymentCapacityAt_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    (carryTwoPaymentClaimFiberAt n j).card ≤ extraPaymentCapacityAt n j := by
  have hclaim := carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty n j h hempty
  have hcapacity := one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty h
  omega

/-- A debt-free universal block has nonpositive signed width drift. -/
theorem universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    universalPaymentBlockSignedDriftAt n j ≤ 0 := by
  rw [universalPaymentBlockSignedDriftAt]
  apply sub_nonpos.mpr
  exact_mod_cast
    carryTwoPaymentClaimFiberAt_card_le_extraPaymentCapacityAt_of_growthDebtFiber_eq_empty
      n j h hempty

/-- Consequently, a debt-free universal block cannot increase bit width. -/
theorem bitWidth_iterateT_le_of_universalPaymentBlock_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    bitWidth (iterateT (j + 1) n).1 ≤
      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
  have hdrift := universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n j h] at hdrift
  omega

/-- In a debt-free universal block, the complete claim count is one exactly at a carry-two endpoint. -/
theorem carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    (carryTwoPaymentClaimFiberAt n j).card = 1 ↔ CarryTwoDebtAt n j := by
  rw [carryTwoPaymentClaimFiberAt_eq_endpoint_singleton_or_empty_of_growthDebtFiber_eq_empty
    n j h hempty]
  unfold endpointCarryTwoClaimShape
  classical
  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]

/-- At a nonempty universal endpoint, capacity one means exact observed height two. -/
theorem extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty
    {n : OddNat} {j : ℕ} (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    extraPaymentCapacityAt n j = 1 ↔ orbitWindowHeight n j = 2 := by
  unfold extraPaymentCapacityAt
  have hheight := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
  omega

/--
For a debt-free universal block, zero drift occurs exactly when the endpoint
contributes its sole carry-two claim and has exactly one unit of capacity.
-/
theorem universalPaymentBlockSignedDriftAt_eq_zero_iff_carryTwo_and_height_eq_two_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅) :
    universalPaymentBlockSignedDriftAt n j = 0 ↔
      CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2 := by
  constructor
  · intro hzero
    have hbalance := (universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity n j).mp hzero
    have hclaim := carryTwoPaymentClaimFiberAt_card_le_one_of_growthDebtFiber_eq_empty n j h hempty
    have hcapacity := one_le_extraPaymentCapacityAt_of_orbitPaymentSourceFiberAt_nonempty h
    have hclaimone : (carryTwoPaymentClaimFiberAt n j).card = 1 := by omega
    have hcapacityone : extraPaymentCapacityAt n j = 1 := by omega
    exact ⟨(carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
      n j h hempty).mp hclaimone,
      (extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty h).mp hcapacityone⟩
  · rintro ⟨hcarry, hheight⟩
    apply (universalPaymentBlockSignedDriftAt_eq_zero_iff_claim_card_eq_capacity n j).mpr
    rw [(carryTwoPaymentClaimFiberAt_card_eq_one_iff_carryTwoDebtAt_of_growthDebtFiber_eq_empty
      n j h hempty).mpr hcarry,
      (extraPaymentCapacityAt_eq_one_iff_orbitWindowHeight_eq_two_of_nonempty h).mpr hheight]

/--
Every other debt-free universal block has strictly negative signed drift.
This is the exact complement of the equality classification, not a global
statement about blocks with delayed-debt sources.
-/
theorem universalPaymentBlockSignedDriftAt_neg_of_not_carryTwo_or_height_ne_two_of_growthDebtFiber_eq_empty
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅)
    (hneq : ¬ (CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2)) :
    universalPaymentBlockSignedDriftAt n j < 0 := by
  have hnonpos := universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
  have hne : universalPaymentBlockSignedDriftAt n j ≠ 0 := by
    intro hzero
    exact hneq ((universalPaymentBlockSignedDriftAt_eq_zero_iff_carryTwo_and_height_eq_two_of_growthDebtFiber_eq_empty
      n j h hempty).mp hzero)
  omega

/-- Every non-equality debt-free universal block strictly decreases bit width. -/
theorem bitWidth_iterateT_lt_of_universalPaymentBlock_not_carryTwo_or_height_ne_two
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hempty : floatGrowthDebtFiberAt n j = ∅)
    (hneq : ¬ (CarryTwoDebtAt n j ∧ orbitWindowHeight n j = 2)) :
    bitWidth (iterateT (j + 1) n).1 <
      bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 := by
  exact (universalPaymentBlockSignedDriftAt_neg_iff_bitWidth_gt n j h).mp
    (universalPaymentBlockSignedDriftAt_neg_of_not_carryTwo_or_height_ne_two_of_growthDebtFiber_eq_empty
      n j h hempty hneq)

/-!
## Delayed-debt necessity and complete-claim decomposition
-/

/-- Strict positive universal block drift requires at least one delayed growth debt. -/
theorem floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hpos : 0 < universalPaymentBlockSignedDriftAt n j) :
    (floatGrowthDebtFiberAt n j).Nonempty := by
  by_contra hnot
  have hempty : floatGrowthDebtFiberAt n j = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  have hnonpos :=
    universalPaymentBlockSignedDriftAt_nonpos_of_growthDebtFiber_eq_empty n j h hempty
  omega

/-- Strict width growth across a universal block requires delayed growth debt support. -/
theorem floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlock_bitWidth_lt
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty)
    (hlt : bitWidth (iterateT (universalPaymentBlockStart n j h) n).1 <
      bitWidth (iterateT (j + 1) n).1) :
    (floatGrowthDebtFiberAt n j).Nonempty := by
  apply floatGrowthDebtFiberAt_nonempty_of_universalPaymentBlockSignedDriftAt_pos n j h
  exact (universalPaymentBlockSignedDriftAt_pos_iff_bitWidth_lt n j h).mpr hlt

/-- Endpoint-only immediate carry-two claim fiber. -/
noncomputable abbrev endpointImmediateCarryTwoClaimFiberAt
    (n : OddNat) (j : ℕ) : Finset ℕ :=
  endpointCarryTwoClaimShape n j

/-- Membership API for the endpoint immediate-claim fiber. -/
theorem mem_endpointImmediateCarryTwoClaimFiberAt_iff
    {n : OddNat} {i j : ℕ} :
    i ∈ endpointImmediateCarryTwoClaimFiberAt n j ↔
      i = j ∧ CarryTwoDebtAt n j := by
  classical
  unfold endpointImmediateCarryTwoClaimFiberAt endpointCarryTwoClaimShape
  by_cases hcarry : CarryTwoDebtAt n j <;> simp [hcarry]

/-- Delayed debts targeting a universal endpoint are exactly its interior carry-two sources. -/
theorem mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
    i ∈ floatGrowthDebtFiberAt n j ↔
      i ∈ Finset.Ico (universalPaymentBlockStart n j h) j ∧ CarryTwoDebtAt n i := by
  constructor
  · intro hi
    have hblock := mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi
    rcases Finset.mem_Icc.mp (by
      rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
      exact hblock) with ⟨hstart, hij⟩
    have hijlt := lt_of_mem_floatGrowthDebtFiberAt hi
    have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hi).2.1
    exact ⟨Finset.mem_Ico.mpr ⟨hstart, hijlt⟩,
      ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt).1⟩
  · rintro ⟨hinterior, hcarry⟩
    rcases Finset.mem_Ico.mp hinterior with ⟨hstart, hij⟩
    have hheight := orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior hinterior
    have hdebt : FloatDebtAt n i :=
      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
    have htarget : floatDebtPaymentTarget n i = j := by
      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hij
    exact mem_floatGrowthDebtFiberAt_iff.mpr
      ⟨Nat.lt_succ_of_lt hij, hdebt, htarget⟩

/-- Every complete claim is either delayed interior debt or the endpoint immediate claim. -/
theorem mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
    {n : OddNat} {i j : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty} :
    i ∈ carryTwoPaymentClaimFiberAt n j ↔
      i ∈ floatGrowthDebtFiberAt n j ∨
        i ∈ endpointImmediateCarryTwoClaimFiberAt n j := by
  rw [mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
      (h := h),
    mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
      (h := h),
    mem_endpointImmediateCarryTwoClaimFiberAt_iff]
  constructor
  · rintro ⟨hblock, hcarry⟩
    rcases (Finset.mem_Icc.mp hblock).2.eq_or_lt with heq | hlt
    · right
      exact ⟨heq, by simpa [heq] using hcarry⟩
    · left
      exact ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hblock).1, hlt⟩, hcarry⟩
  · rintro (hinteriorCarry | hendpoint)
    · rcases hinteriorCarry with ⟨hinterior, hcarry⟩
      exact ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ico.mp hinterior).1, (Finset.mem_Ico.mp hinterior).2.le⟩,
        hcarry⟩
    · rcases hendpoint with ⟨hij, hcarry⟩
      subst i
      have hstartmem := universalPaymentBlockStart_mem_sourceFiber n j h
      exact ⟨Finset.mem_Icc.mpr
        ⟨(mem_orbitPaymentSourceFiberAt_iff.mp hstartmem).1, le_rfl⟩, hcarry⟩

/-- Disjoint complete-claim decomposition into delayed and immediate support. -/
theorem carryTwoPaymentClaimFiberAt_eq_growthDebt_union_endpointImmediate
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    carryTwoPaymentClaimFiberAt n j =
      floatGrowthDebtFiberAt n j ∪ endpointImmediateCarryTwoClaimFiberAt n j := by
  ext i
  simp only [Finset.mem_union]
  exact mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
    (h := h)

/-- Delayed debt support and the endpoint immediate claim are disjoint. -/
theorem disjoint_floatGrowthDebtFiberAt_endpointImmediateCarryTwoClaimFiberAt
    (n : OddNat) (j : ℕ) :
    Disjoint (floatGrowthDebtFiberAt n j) (endpointImmediateCarryTwoClaimFiberAt n j) := by
  rw [Finset.disjoint_left]
  intro i hidebt hiend
  have hlt := lt_of_mem_floatGrowthDebtFiberAt hidebt
  have heq := (mem_endpointImmediateCarryTwoClaimFiberAt_iff.mp hiend).1
  omega

/-- Exact claim-card decomposition into delayed support and one optional endpoint claim. -/
theorem carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    (carryTwoPaymentClaimFiberAt n j).card =
      (floatGrowthDebtFiberAt n j).card +
        (endpointImmediateCarryTwoClaimFiberAt n j).card := by
  rw [carryTwoPaymentClaimFiberAt_eq_growthDebt_union_endpointImmediate n j h,
    Finset.card_union_of_disjoint
      (disjoint_floatGrowthDebtFiberAt_endpointImmediateCarryTwoClaimFiberAt n j)]

/-- Refined signed drift: delayed claims plus endpoint claim minus endpoint capacity. -/
theorem universalPaymentBlockSignedDriftAt_eq_growthDebt_add_endpoint_sub_capacity
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockSignedDriftAt n j =
      (floatGrowthDebtFiberAt n j).card +
        (endpointImmediateCarryTwoClaimFiberAt n j).card -
          extraPaymentCapacityAt n j := by
  unfold universalPaymentBlockSignedDriftAt
  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card n j h]
  norm_num

/-- Universal and debt-supported starts have the same bit width. -/
theorem bitWidth_universalPaymentBlockStart_eq_floatPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    bitWidth (iterateT (universalPaymentBlockStart n j
      (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h)) n).1 =
        bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 := by
  have hu := bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card n j
    (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h)
  have hd := bitWidth_iterateT_paymentBlock_eq_claimFiber_card n j h
  omega

/-- The prefix between universal and debt-supported starts has observed height one. -/
theorem orbitWindowHeight_eq_one_between_universal_and_floatPaymentBlockStart
    {n : OddNat} {j i : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
    (hi : i ∈ Finset.Ico
      (universalPaymentBlockStart n j
        (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h))
      (floatPaymentBlockStart n j h)) :
    orbitWindowHeight n i = 1 := by
  rcases Finset.mem_Ico.mp hi with ⟨hstart, hib⟩
  have hbj := floatPaymentBlockStart_lt_endpoint n j h
  exact orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
    (Finset.mem_Ico.mpr ⟨hstart, hib.trans hbj⟩)

/-- The prefix between universal and debt-supported starts has upper carry one. -/
theorem stateUpperCarry_eq_one_between_universal_and_floatPaymentBlockStart
    {n : OddNat} {j i : ℕ} {h : (floatGrowthDebtFiberAt n j).Nonempty}
    (hi : i ∈ Finset.Ico
      (universalPaymentBlockStart n j
        (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h))
      (floatPaymentBlockStart n j h)) :
    stateUpperCarry (iterateT i n).1 = 1 := by
  have hheight := orbitWindowHeight_eq_one_between_universal_and_floatPaymentBlockStart hi
  have hnotcarry : ¬ CarryTwoDebtAt n i := by
    intro hcarry
    rcases Finset.mem_Ico.mp hi with ⟨hstart, hib⟩
    have hbj := floatPaymentBlockStart_lt_endpoint n j h
    have htarget : floatDebtPaymentTarget n i = j := by
      simpa [floatDebtPaymentTarget_eq_orbitPaymentTarget] using
        orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart (hib.trans hbj)
    have hdebt : FloatDebtAt n i :=
      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr ⟨hcarry, hheight⟩
    have hfiber : i ∈ floatGrowthDebtFiberAt n j :=
      mem_floatGrowthDebtFiberAt_iff.mpr
        ⟨Nat.lt_succ_of_lt (hib.trans hbj), hdebt, htarget⟩
    have hminle : floatPaymentBlockStart n j h ≤ i := Finset.min'_le _ _ hfiber
    omega
  have hpos : 0 < (iterateT i n).1 := by
    have hodd := (iterateT i n).2
    omega
  rcases stateUpperCarry_one_or_two hpos with hone | htwo
  · exact hone
  · exact False.elim (hnotcarry htwo)

/-!
## Canonical endpoint sequence

The sequence records the first payment endpoint, then the target immediately
after each endpoint.  It is defined without choosing a proof of fiber
nonemptiness; the target map itself supplies the endpoint property.
-/

/-- Canonical successive endpoints of universal payment blocks. -/
noncomputable def paymentEndpointSeq (n : OddNat) : ℕ → ℕ
  | 0 => orbitPaymentTarget n 0
  | k + 1 => orbitPaymentTarget n (paymentEndpointSeq n k + 1)

/-- Every canonical sequence entry is an extra-height endpoint. -/
theorem two_le_orbitWindowHeight_paymentEndpointSeq
    (n : OddNat) (k : ℕ) :
    2 ≤ orbitWindowHeight n (paymentEndpointSeq n k) := by
  cases k with
  | zero =>
      simpa [paymentEndpointSeq] using two_le_orbitWindowHeight_orbitPaymentTarget n 0
  | succ k =>
      simpa [paymentEndpointSeq] using
        two_le_orbitWindowHeight_orbitPaymentTarget n (paymentEndpointSeq n k + 1)

/-- Each canonical sequence entry is fixed by the universal target map. -/
theorem orbitPaymentTarget_paymentEndpointSeq
    (n : OddNat) (k : ℕ) :
    orbitPaymentTarget n (paymentEndpointSeq n k) = paymentEndpointSeq n k := by
  apply orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
  exact two_le_orbitWindowHeight_paymentEndpointSeq n k

/-- Consecutive canonical payment endpoints are strictly increasing. -/
theorem paymentEndpointSeq_lt_succ
    (n : OddNat) (k : ℕ) :
    paymentEndpointSeq n k < paymentEndpointSeq n (k + 1) := by
  rw [show paymentEndpointSeq n (k + 1) =
    orbitPaymentTarget n (paymentEndpointSeq n k + 1) by rfl]
  have hlt := orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
    (two_le_orbitWindowHeight_paymentEndpointSeq n k)
  rw [orbitPaymentTarget_paymentEndpointSeq] at hlt
  exact hlt

/-- Every sequence endpoint has a nonempty universal source fiber. -/
theorem orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq
    (n : OddNat) (k : ℕ) :
    (orbitPaymentSourceFiberAt n (paymentEndpointSeq n k)).Nonempty :=
  (orbitPaymentSourceFiberAt_nonempty_iff_two_le_orbitWindowHeight n
    (paymentEndpointSeq n k)).mpr (two_le_orbitWindowHeight_paymentEndpointSeq n k)

/-- The first canonical payment block starts at orbit time zero. -/
theorem universalPaymentBlockStart_paymentEndpointSeq_zero
    (n : OddNat) :
    universalPaymentBlockStart n (paymentEndpointSeq n 0)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n 0) = 0 := by
  have hzero : 0 ∈ orbitPaymentSourceFiberAt n (paymentEndpointSeq n 0) := by
    rw [mem_orbitPaymentSourceFiberAt_iff_target_eq]
    rfl
  unfold universalPaymentBlockStart
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hzero)

/--
The next canonical block starts immediately after the previous endpoint.
Monotonicity rules out an earlier source: every index at most the old endpoint
still targets at most that old endpoint, whereas the next target is strictly
larger.
-/
theorem universalPaymentBlockStart_paymentEndpointSeq_succ
    (n : OddNat) (k : ℕ) :
    universalPaymentBlockStart n (paymentEndpointSeq n (k + 1))
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1)) =
        paymentEndpointSeq n k + 1 := by
  let e := paymentEndpointSeq n k
  let e' := paymentEndpointSeq n (k + 1)
  let h' := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n (k + 1)
  let b := universalPaymentBlockStart n e' h'
  have hsource : e + 1 ∈ orbitPaymentSourceFiberAt n e' := by
    rw [mem_orbitPaymentSourceFiberAt_iff_target_eq]
    change orbitPaymentTarget n (paymentEndpointSeq n k + 1) = paymentEndpointSeq n (k + 1)
    rfl
  have hble : b ≤ e + 1 := Finset.min'_le _ _ hsource
  have hbtarget : orbitPaymentTarget n b = e' :=
    (mem_orbitPaymentSourceFiberAt_iff.mp
      (universalPaymentBlockStart_mem_sourceFiber n e' h')).2
  by_contra hne
  have hblt : b < e + 1 := lt_of_le_of_ne hble hne
  have hbe : b ≤ e := by omega
  have hmono : orbitPaymentTarget n b ≤ orbitPaymentTarget n e :=
    monotone_orbitPaymentTarget n hbe
  have hefix : orbitPaymentTarget n e = e := by
    dsimp [e]
    exact orbitPaymentTarget_paymentEndpointSeq n k
  have hee' : e < e' := by
    dsimp [e, e']
    exact paymentEndpointSeq_lt_succ n k
  omega

/-- The cardinality of a universal payment block is its interval length. -/
theorem orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    (orbitPaymentSourceFiberAt n j).card =
      j - universalPaymentBlockStart n j h + 1 := by
  rw [orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n j h]
  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
  have hle : universalPaymentBlockStart n j h ≤ j :=
    (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
  simp
  omega

/-- The universal block cardinality is the exact depth of its earliest source. -/
theorem orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_start
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    (orbitPaymentSourceFiberAt n j).card =
      orbitExactDepth n (universalPaymentBlockStart n j h) := by
  rw [orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one n j h]
  have hstart := universalPaymentBlockStart_mem_sourceFiber n j h
  have hle : universalPaymentBlockStart n j h ≤ j :=
    (mem_orbitPaymentSourceFiberAt_iff.mp hstart).1
  exact (orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
    (Finset.mem_Icc.mpr ⟨le_rfl, hle⟩)).symm

/-!
## Current frontier

Universal payment-block geometry is complete: target fibers are contiguous
intervals with a descending exact-depth profile.  The remaining work is
accounting over universal blocks and finite families of them: identify their
complete claim fibers and endpoint capacity, prove their direct ledger, then
retain an explicit unfinished suffix in finite-prefix decompositions.
-/

end DkMath.Collatz
