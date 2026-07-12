/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge"

namespace DkMath.Collatz

/-!
# Delayed-payment multiplicity

This module separates three different coordinates which must not be identified:

* source time `i`;
* exact all-ones depth `A_i`;
* payment time `i + A_i - 1`.

The target map is deliberately allowed to be noninjective.  Its fibers record
the multiplicity that a later capacity theorem must compare with the extra
height available at the target slot.
-/

/-- The exact all-ones depth at an orbit time. -/
noncomputable def orbitExactDepth (n : OddNat) (i : ℕ) : ℕ :=
  ResidualAllOnesDepth (oddOrbitLabel n i)

/-- The deterministic delayed-payment target of a Float width-growth debt. -/
noncomputable def floatDebtPaymentTarget (n : OddNat) (i : ℕ) : ℕ :=
  i + orbitExactDepth n i - 1

/-- Exact recovery at depth at least two is an exact-height-one source event. -/
theorem orbitDepthRecoversExactlyAt_height_eq_one
    (n : OddNat) (i d : ℕ)
    (hd : 2 ≤ d)
    (h : OrbitDepthRecoversExactlyAt n i d) :
    orbitWindowHeight n i = 1 := by
  have hrec := (orbitDepthRecoversExactlyAt_iff_recoverySibling n i d).1 h
  apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).2
  have hfour : 4 ∣ 2 ^ (d + 1) := by
    rcases exists_add_of_le hd with ⟨e, he⟩
    rw [he, show (2 + e + 1 : ℕ) = 2 + (e + 1) by omega, pow_add]
    norm_num
  rw [mod_eq_mod_of_dvd_modulus hfour, hrec]
  rcases exists_add_of_le hd with ⟨e, he⟩
  rw [he, pow_add]
  have hpow : 0 < 2 ^ e := pow_pos (by norm_num) e
  have hsplit : 4 * 2 ^ e - 1 = 3 + (2 ^ e - 1) * 4 := by omega
  norm_num
  rw [hsplit, Nat.add_mul_mod_self_right]

/--
The complete exact-depth staircase before its forced extra-height payment.

For every proper pre-payment offset, the remaining depth is exact and the
observed height is exactly one.  The endpoint is separately known to have
height at least two.
-/
theorem orbitDepthRecoversExactlyAt_prePayment_chain
    (n : OddNat) (i d : ℕ)
    (hd : 2 ≤ d)
    (hexact : OrbitDepthRecoversExactlyAt n i d) :
    (∀ t, t < d - 1 →
      OrbitDepthRecoversExactlyAt n (i + t) (d - t) ∧
        orbitWindowHeight n (i + t) = 1) ∧
      2 ≤ orbitWindowHeight n (i + d - 1) := by
  have hstair : ∀ t, t ≤ d - 2 →
      OrbitDepthRecoversExactlyAt n (i + t) (d - t) := by
    intro t ht
    induction t with
    | zero => simpa using hexact
    | succ t iht =>
      have ht' : t ≤ d - 2 := by omega
      have hprev := iht ht'
      have hdepth : 3 ≤ d - t := by omega
      have hnext := orbitDepthRecoversExactlyAt_succ_of_three_le
        n (i + t) (d - t) hdepth hprev
      simpa [show i + (t + 1) = i + t + 1 by omega,
        show d - (t + 1) = (d - t) - 1 by omega] using hnext
  constructor
  · intro t ht
    have ht' : t ≤ d - 2 := by omega
    have hrec := hstair t ht'
    refine ⟨hrec, orbitDepthRecoversExactlyAt_height_eq_one n (i + t) (d - t) ?_ hrec⟩
    omega
  · exact orbitDepthRecoversExactlyAt_delayed_height_two_le n i d hd hexact

/-- The discharge relation has the unique canonical target fixed by exact depth. -/
theorem floatDebtPaymentDischarge_target_eq
    {n : OddNat} {i j : ℕ}
    (h : FloatDebtPaymentDischarge n i j) :
    j = floatDebtPaymentTarget n i := by
  rcases h with ⟨_, depth, _, hexact, hj, _⟩
  have hdepth : depth = orbitExactDepth n i := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact.symm
  rw [hdepth] at hj
  simpa [floatDebtPaymentTarget] using hj

/-- Every Float growth debt reaches its canonical delayed-payment target. -/
theorem floatDebtAt_paymentDischarge_target
    {n : OddNat} {i : ℕ}
    (h : FloatDebtAt n i) :
    FloatDebtPaymentDischarge n i (floatDebtPaymentTarget n i) := by
  rcases floatDebtAt_exists_paymentDischarge n i h with ⟨j, hj⟩
  rw [floatDebtPaymentDischarge_target_eq hj] at hj
  exact hj

/-- The proof-carrying delayed discharge relation is the graph of the target map. -/
theorem floatDebtPaymentDischarge_iff_target
    {n : OddNat} {i j : ℕ} :
    FloatDebtPaymentDischarge n i j ↔
      FloatDebtAt n i ∧ j = floatDebtPaymentTarget n i := by
  constructor
  · intro h
    exact ⟨h.1, floatDebtPaymentDischarge_target_eq h⟩
  · rintro ⟨hdebt, htarget⟩
    rw [htarget]
    exact floatDebtAt_paymentDischarge_target hdebt

/-- The canonical target is an actual extra-height payment for every Float debt. -/
theorem floatDebtAt_paymentTarget
    {n : OddNat} {i : ℕ}
    (h : FloatDebtAt n i) :
    PetalPaymentAt n (floatDebtPaymentTarget n i) := by
  rcases floatDebtAt_paymentDischarge_target h with ⟨_, _, _, _, _, hpay⟩
  exact hpay

/-- A Float growth debt is strictly before its delayed payment target. -/
theorem floatDebtAt_lt_paymentTarget
    {n : OddNat} {i : ℕ}
    (h : FloatDebtAt n i) :
    i < floatDebtPaymentTarget n i := by
  rcases floatDebtAt_paymentDischarge_target h with ⟨_, depth, hdepth, _, htarget, _⟩
  rw [htarget]
  omega

/-- Finite fiber of Float debts having canonical delayed payment target `j`. -/
noncomputable def floatGrowthDebtFiberAt
    (n : OddNat) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (j + 1)).filter fun i =>
    FloatDebtAt n i ∧ floatDebtPaymentTarget n i = j

/-- Membership in a delayed-growth debt fiber. -/
theorem mem_floatGrowthDebtFiberAt_iff
    {n : OddNat} {i j : ℕ} :
    i ∈ floatGrowthDebtFiberAt n j ↔
      i < j + 1 ∧ FloatDebtAt n i ∧ floatDebtPaymentTarget n i = j := by
  simp [floatGrowthDebtFiberAt]

/-- Every debt in the fiber is strictly earlier than its payment slot. -/
theorem lt_of_mem_floatGrowthDebtFiberAt
    {n : OddNat} {i j : ℕ}
    (h : i ∈ floatGrowthDebtFiberAt n j) :
    i < j := by
  rcases (mem_floatGrowthDebtFiberAt_iff.mp h) with ⟨_, hdebt, htarget⟩
  rw [← htarget]
  exact floatDebtAt_lt_paymentTarget hdebt

/-- A canonical debt belongs to the fiber over its own payment target. -/
theorem mem_floatGrowthDebtFiberAt_paymentTarget
    {n : OddNat} {i : ℕ}
    (h : FloatDebtAt n i) :
    i ∈ floatGrowthDebtFiberAt n (floatDebtPaymentTarget n i) := by
  apply mem_floatGrowthDebtFiberAt_iff.mpr
  exact ⟨Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget h), h, rfl⟩

/-- A target collision gives two distinct elements of its canonical debt fiber. -/
theorem FloatPaymentCollisionAt.exists_distinct_mem_growthDebtFiber
    {n : OddNat} {j : ℕ}
    (h : FloatPaymentCollisionAt n j) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧
      i₁ ∈ floatGrowthDebtFiberAt n j ∧ i₂ ∈ floatGrowthDebtFiberAt n j := by
  rcases h with ⟨i₁, i₂, hne, h₁, h₂⟩
  refine ⟨i₁, i₂, hne, ?_, ?_⟩
  · apply mem_floatGrowthDebtFiberAt_iff.mpr
    rcases h₁ with ⟨hdebt, depth, _, _, htarget, _⟩
    exact ⟨by omega, hdebt,
      (floatDebtPaymentDischarge_target_eq
        ⟨hdebt, depth, by omega, by assumption, htarget, by assumption⟩).symm⟩
  · apply mem_floatGrowthDebtFiberAt_iff.mpr
    rcases h₂ with ⟨hdebt, depth, _, _, htarget, _⟩
    exact ⟨by omega, hdebt,
      (floatDebtPaymentDischarge_target_eq
        ⟨hdebt, depth, by omega, by assumption, htarget, by assumption⟩).symm⟩

/-- A target collision is exactly a delayed-growth debt fiber of size at least two. -/
theorem floatPaymentCollisionAt_iff_two_le_growthDebtFiberCard
    {n : OddNat} {j : ℕ} :
    FloatPaymentCollisionAt n j ↔ 2 ≤ (floatGrowthDebtFiberAt n j).card := by
  constructor
  · intro h
    rcases h.exists_distinct_mem_growthDebtFiber with ⟨i₁, i₂, hne, hi₁, hi₂⟩
    have hcard : 1 < (floatGrowthDebtFiberAt n j).card :=
      Finset.one_lt_card.mpr ⟨i₁, hi₁, i₂, hi₂, hne⟩
    omega
  · intro hcard
    rcases Finset.one_lt_card.mp (by omega : 1 < (floatGrowthDebtFiberAt n j).card)
      with ⟨i₁, hi₁, i₂, hi₂, hne⟩
    rcases mem_floatGrowthDebtFiberAt_iff.mp hi₁ with ⟨_, hdebt₁, htarget₁⟩
    rcases mem_floatGrowthDebtFiberAt_iff.mp hi₂ with ⟨_, hdebt₂, htarget₂⟩
    refine ⟨i₁, i₂, hne, ?_, ?_⟩
    · have hdischarge := floatDebtAt_paymentDischarge_target hdebt₁
      rwa [htarget₁] at hdischarge
    · have hdischarge := floatDebtAt_paymentDischarge_target hdebt₂
      rwa [htarget₂] at hdischarge

/-- The number of extra height units available at a payment time. -/
noncomputable def extraPaymentCapacityAt (n : OddNat) (j : ℕ) : ℕ :=
  orbitWindowHeight n j - 1

/-- More delayed growth-debt claims than available extra-height capacity. -/
def FloatPaymentOverloadAt (n : OddNat) (j : ℕ) : Prop :=
  extraPaymentCapacityAt n j < (floatGrowthDebtFiberAt n j).card

/-- A payment slot with a nonempty delayed-debt fiber has at least one extra unit. -/
theorem one_le_extraPaymentCapacityAt_of_growthDebtFiber_nonempty
    {n : OddNat} {j : ℕ}
    (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    1 ≤ extraPaymentCapacityAt n j := by
  rcases h with ⟨i, hi⟩
  rcases (mem_floatGrowthDebtFiberAt_iff.mp hi) with ⟨_, hdebt, htarget⟩
  have hpay := floatDebtAt_paymentTarget hdebt
  rw [htarget] at hpay
  unfold extraPaymentCapacityAt PetalPaymentAt at *
  omega

/-- A genuine delayed-payment overload forces a target collision. -/
theorem floatPaymentOverloadAt_implies_collision
    {n : OddNat} {j : ℕ}
    (h : FloatPaymentOverloadAt n j) :
    FloatPaymentCollisionAt n j := by
  have hcard_pos : 0 < (floatGrowthDebtFiberAt n j).card := by
    unfold FloatPaymentOverloadAt at h
    omega
  have hnonempty : (floatGrowthDebtFiberAt n j).Nonempty :=
    Finset.card_pos.mp hcard_pos
  have hcap : 1 ≤ extraPaymentCapacityAt n j :=
    one_le_extraPaymentCapacityAt_of_growthDebtFiber_nonempty hnonempty
  have htwo : 2 ≤ (floatGrowthDebtFiberAt n j).card := by
    unfold FloatPaymentOverloadAt at h
    omega
  exact floatPaymentCollisionAt_iff_two_le_growthDebtFiberCard.mpr htwo

/-- Every Float debt has all-ones depth at least two. -/
theorem two_le_orbitExactDepth_of_floatDebtAt
    {n : OddNat} {i : ℕ}
    (h : FloatDebtAt n i) :
    2 ≤ orbitExactDepth n i := by
  rcases floatDebtAt_paymentDischarge_target h with ⟨_, depth, hdepth, hexact, _, _⟩
  have heq : depth = orbitExactDepth n i := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact.symm
  omega

/-- Equal canonical targets form one descending exact-depth diagonal. -/
theorem orbitExactDepth_eq_add_gap_of_lt_paymentTarget_eq
    {n : OddNat} {i₁ i₂ : ℕ}
    (hlt : i₁ < i₂)
    (hdepth₁ : 1 ≤ orbitExactDepth n i₁)
    (hdepth₂ : 1 ≤ orbitExactDepth n i₂)
    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
    orbitExactDepth n i₁ = orbitExactDepth n i₂ + (i₂ - i₁) := by
  unfold floatDebtPaymentTarget at htarget
  omega

/-- Two ordered Float debts with one target lie on one descending depth diagonal. -/
theorem floatDebtAt_orbitExactDepth_eq_add_gap_of_lt_same_paymentTarget
    {n : OddNat} {i₁ i₂ : ℕ}
    (hi₁ : FloatDebtAt n i₁)
    (hi₂ : FloatDebtAt n i₂)
    (hlt : i₁ < i₂)
    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
    orbitExactDepth n i₁ = orbitExactDepth n i₂ + (i₂ - i₁) := by
  apply orbitExactDepth_eq_add_gap_of_lt_paymentTarget_eq hlt
  · have hdepth := two_le_orbitExactDepth_of_floatDebtAt hi₁
    omega
  · have hdepth := two_le_orbitExactDepth_of_floatDebtAt hi₂
    omega
  · exact htarget

/--
Two ordered Float debts with a common target occupy one exact-depth staircase.

Every intermediate time from the earlier source to the later source remains in
the pre-payment height-one chain; at the later source the remaining depth is
exactly its own all-ones depth.
-/
theorem floatDebtAt_same_paymentTarget_staircase_to_later_source
    {n : OddNat} {i₁ i₂ : ℕ}
    (hi₁ : FloatDebtAt n i₁)
    (hi₂ : FloatDebtAt n i₂)
    (hlt : i₁ < i₂)
    (htarget : floatDebtPaymentTarget n i₁ = floatDebtPaymentTarget n i₂) :
    (∀ t, t ≤ i₂ - i₁ →
      OrbitDepthRecoversExactlyAt n (i₁ + t) (orbitExactDepth n i₁ - t) ∧
        orbitWindowHeight n (i₁ + t) = 1) ∧
      OrbitDepthRecoversExactlyAt n i₂ (orbitExactDepth n i₂) := by
  have hdepth₁ := two_le_orbitExactDepth_of_floatDebtAt hi₁
  have hdepth₂ := two_le_orbitExactDepth_of_floatDebtAt hi₂
  have hdiag := floatDebtAt_orbitExactDepth_eq_add_gap_of_lt_same_paymentTarget
    hi₁ hi₂ hlt htarget
  have hgap : i₂ - i₁ < orbitExactDepth n i₁ - 1 := by
    omega
  have hexact₁ : OrbitDepthRecoversExactlyAt n i₁ (orbitExactDepth n i₁) := by
    rfl
  rcases orbitDepthRecoversExactlyAt_prePayment_chain n i₁ (orbitExactDepth n i₁)
      hdepth₁ hexact₁ with ⟨hchain, _⟩
  constructor
  · intro t ht
    have hlt' : t < orbitExactDepth n i₁ - 1 := lt_of_le_of_lt ht hgap
    exact hchain t hlt'
  · have hlater := (hchain (i₂ - i₁) hgap).1
    simpa [show i₁ + (i₂ - i₁) = i₂ by omega, hdiag] using hlater

/-- A carry-two event is every upper binary carry requiring one extra unit. -/
def CarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
  stateUpperCarry (iterateT i n).1 = 2

/-- A carry-two event is delayed precisely when its observed height is one. -/
def DelayedCarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
  CarryTwoDebtAt n i ∧ orbitWindowHeight n i = 1

/-- A carry-two event self-pays immediately when its height is already extra. -/
def ImmediateCarryTwoDebtAt (n : OddNat) (i : ℕ) : Prop :=
  CarryTwoDebtAt n i ∧ 2 ≤ orbitWindowHeight n i

/-- Float width growth is exactly the delayed carry-two branch. -/
theorem floatDebtAt_iff_delayedCarryTwoDebtAt
    (n : OddNat) (i : ℕ) :
    FloatDebtAt n i ↔ DelayedCarryTwoDebtAt n i := by
  unfold FloatDebtAt DelayedCarryTwoDebtAt CarryTwoDebtAt
  rw [iterateT_succ_eq_T_iterateT]
  rw [bitWidth_growth_iff_carryTwo_and_heightOne]
  simp only [orbitWindowHeight_eq_s_iterateT]

/-- Every carry-two event is either delayed or immediately self-paid. -/
theorem carryTwoDebtAt_delayed_or_immediate
    {n : OddNat} {i : ℕ}
    (h : CarryTwoDebtAt n i) :
    DelayedCarryTwoDebtAt n i ∨ ImmediateCarryTwoDebtAt n i := by
  by_cases hone : orbitWindowHeight n i = 1
  · exact Or.inl ⟨h, hone⟩
  · right
    refine ⟨h, ?_⟩
    have hpos := orbitWindowHeight_one_le n i
    omega

/-- Complete claim relation for the carry-two ledger. -/
noncomputable def CarryTwoPaymentClaim
    (n : OddNat) (i j : ℕ) : Prop :=
  DelayedCarryTwoDebtAt n i ∧ j = floatDebtPaymentTarget n i ∨
    ImmediateCarryTwoDebtAt n i ∧ j = i

/-- Every carry-two event makes one explicit payment claim. -/
theorem carryTwoDebtAt_exists_paymentClaim
    {n : OddNat} {i : ℕ}
    (h : CarryTwoDebtAt n i) :
    ∃ j, CarryTwoPaymentClaim n i j := by
  rcases carryTwoDebtAt_delayed_or_immediate h with hdelayed | himmediate
  · refine ⟨floatDebtPaymentTarget n i, Or.inl ⟨hdelayed, rfl⟩⟩
  · exact ⟨i, Or.inr ⟨himmediate, rfl⟩⟩

/-- Finite fiber of all carry-two claims arriving at one payment slot. -/
noncomputable def carryTwoPaymentClaimFiberAt
    (n : OddNat) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (j + 1)).filter fun i => CarryTwoPaymentClaim n i j

/-- Membership in the finite complete carry-two claim fiber. -/
theorem mem_carryTwoPaymentClaimFiberAt_iff
    {n : OddNat} {i j : ℕ} :
    i ∈ carryTwoPaymentClaimFiberAt n j ↔
      i < j + 1 ∧ CarryTwoPaymentClaim n i j := by
  simp [carryTwoPaymentClaimFiberAt]

/-- Every complete carry-two claim reaches an actual extra-height payment slot. -/
theorem carryTwoPaymentClaim_payment
    {n : OddNat} {i j : ℕ}
    (h : CarryTwoPaymentClaim n i j) :
    PetalPaymentAt n j := by
  rcases h with hdelayed | himmediate
  · rcases hdelayed with ⟨hdelayed, htarget⟩
    have hdebt : FloatDebtAt n i :=
      (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
    rw [htarget]
    exact floatDebtAt_paymentTarget hdebt
  · rcases himmediate with ⟨⟨_, hheight⟩, hself⟩
    rw [hself]
    exact hheight

/-- Every complete carry-two claim is present in the finite fiber of its target. -/
theorem mem_carryTwoPaymentClaimFiberAt_of_claim
    {n : OddNat} {i j : ℕ}
    (h : CarryTwoPaymentClaim n i j) :
    i ∈ carryTwoPaymentClaimFiberAt n j := by
  apply mem_carryTwoPaymentClaimFiberAt_iff.mpr
  constructor
  · rcases h with hdelayed | himmediate
    · rcases hdelayed with ⟨hdelayed, htarget⟩
      have hdebt : FloatDebtAt n i :=
        (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mpr hdelayed
      rw [htarget]
      exact Nat.lt_succ_of_lt (floatDebtAt_lt_paymentTarget hdebt)
    · rcases himmediate with ⟨_, hself⟩
      rw [hself]
      exact Nat.lt_succ_self i
  · exact h

/-- A nonempty complete claim fiber has at least one extra-height unit available. -/
theorem one_le_extraPaymentCapacityAt_of_carryTwoClaimFiber_nonempty
    {n : OddNat} {j : ℕ}
    (h : (carryTwoPaymentClaimFiberAt n j).Nonempty) :
    1 ≤ extraPaymentCapacityAt n j := by
  rcases h with ⟨i, hi⟩
  have hclaim := (mem_carryTwoPaymentClaimFiberAt_iff.mp hi).2
  have hpay := carryTwoPaymentClaim_payment hclaim
  unfold extraPaymentCapacityAt PetalPaymentAt at *
  omega

/-- Two distinct carry-two sources claim the same payment slot. -/
def CarryTwoPaymentClaimCollisionAt (n : OddNat) (j : ℕ) : Prop :=
  ∃ i₁ i₂, i₁ ≠ i₂ ∧
    CarryTwoPaymentClaim n i₁ j ∧ CarryTwoPaymentClaim n i₂ j

/-- Complete-claim collision is exactly a complete claim fiber of size at least two. -/
theorem carryTwoPaymentClaimCollisionAt_iff_two_le_fiberCard
    {n : OddNat} {j : ℕ} :
    CarryTwoPaymentClaimCollisionAt n j ↔
      2 ≤ (carryTwoPaymentClaimFiberAt n j).card := by
  constructor
  · rintro ⟨i₁, i₂, hne, h₁, h₂⟩
    have hi₁ := mem_carryTwoPaymentClaimFiberAt_of_claim h₁
    have hi₂ := mem_carryTwoPaymentClaimFiberAt_of_claim h₂
    have hcard : 1 < (carryTwoPaymentClaimFiberAt n j).card :=
      Finset.one_lt_card.mpr ⟨i₁, hi₁, i₂, hi₂, hne⟩
    omega
  · intro hcard
    rcases Finset.one_lt_card.mp
        (by omega : 1 < (carryTwoPaymentClaimFiberAt n j).card)
      with ⟨i₁, hi₁, i₂, hi₂, hne⟩
    refine ⟨i₁, i₂, hne,
      (mem_carryTwoPaymentClaimFiberAt_iff.mp hi₁).2,
      (mem_carryTwoPaymentClaimFiberAt_iff.mp hi₂).2⟩

/-- Capacity overload for the complete carry-two claim ledger. -/
def CarryTwoPaymentOverloadAt (n : OddNat) (j : ℕ) : Prop :=
  extraPaymentCapacityAt n j < (carryTwoPaymentClaimFiberAt n j).card

/-- A complete carry-two payment overload forces a complete-claim collision. -/
theorem carryTwoPaymentOverloadAt_implies_collision
    {n : OddNat} {j : ℕ}
    (h : CarryTwoPaymentOverloadAt n j) :
    CarryTwoPaymentClaimCollisionAt n j := by
  have hcard_pos : 0 < (carryTwoPaymentClaimFiberAt n j).card := by
    unfold CarryTwoPaymentOverloadAt at h
    omega
  have hnonempty : (carryTwoPaymentClaimFiberAt n j).Nonempty :=
    Finset.card_pos.mp hcard_pos
  have hcap : 1 ≤ extraPaymentCapacityAt n j :=
    one_le_extraPaymentCapacityAt_of_carryTwoClaimFiber_nonempty hnonempty
  have htwo : 2 ≤ (carryTwoPaymentClaimFiberAt n j).card := by
    unfold CarryTwoPaymentOverloadAt at h
    omega
  exact carryTwoPaymentClaimCollisionAt_iff_two_le_fiberCard.mpr htwo

/-!
## Current boundary

The finite debt and complete carry-two claim fibers are now explicit.  The
remaining bridge is genuinely combinatorial: compare a target fiber's
multiplicity with `extraPaymentCapacityAt`, then relate an overload to a
localized horizontal continuation/recovery imbalance.  Target coincidence is
not itself an overload, because one payment slot can have several extra height
units.
-/

end DkMath.Collatz
