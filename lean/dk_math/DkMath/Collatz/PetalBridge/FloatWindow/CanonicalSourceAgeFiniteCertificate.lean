/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate"

namespace DkMath.Collatz

/-!
# Finite certificate preparation for the canonical source-age frontier

This module starts the finite-facing layer only after the exact horizon
arithmetic has been fixed.  In particular, it distinguishes an exact finite
word from a projected upper-weight certificate: failure of deterministic
weight recovery does not by itself refute a sound upper projection.
-/

/-! ## Padded finite pre-block carry word -/

/-- The finite carry word immediately before block `m`, listed backwards from
its start.  Offset `r` denotes source `start - (r + 1)` only when that source
exists.  Invalid offsets are explicitly false, so Nat underflow never aliases
several bits to source zero. -/
noncomputable def canonicalPreBlockCarryWord
    (n : OddNat) (H m : ℕ) : Fin H → Bool := by
  classical
  exact fun r => decide
    (r.val + 1 ≤ canonicalBlockStartTime n m ∧
      CarryTwoDebtAt n
        (canonicalBlockStartTime n m - (r.val + 1)))

/-- Offsets whose padded pre-block word contains a carry. -/
noncomputable def canonicalPreBlockCarryTrueOffsets
    (n : OddNat) (H m : ℕ) : Finset (Fin H) := by
  classical
  exact Finset.univ.filter fun r => canonicalPreBlockCarryWord n H m r = true

/-- Number of true bits in the padded pre-block carry word. -/
noncomputable def canonicalPreBlockCarryWordTrueCount
    (n : OddNat) (H m : ℕ) : ℕ :=
  (canonicalPreBlockCarryTrueOffsets n H m).card

@[simp] theorem mem_canonicalPreBlockCarryTrueOffsets_iff
    {n : OddNat} {H m : ℕ} {r : Fin H} :
    r ∈ canonicalPreBlockCarryTrueOffsets n H m ↔
      r.val + 1 ≤ canonicalBlockStartTime n m ∧
        CarryTwoDebtAt n
          (canonicalBlockStartTime n m - (r.val + 1)) := by
  classical
  simp [canonicalPreBlockCarryTrueOffsets, canonicalPreBlockCarryWord]

/-- The padded word counts the actual pre-block carry carrier in every regime,
including block starts smaller than the requested horizon. -/
theorem canonicalPreBlockCarryWordTrueCount_eq_carrier_card
    (n : OddNat) (H m : ℕ) :
    canonicalPreBlockCarryWordTrueCount n H m =
      (canonicalPreBlockCarryCarrier n H m).card := by
  classical
  unfold canonicalPreBlockCarryWordTrueCount
  apply Finset.card_bij
      (fun r _ => canonicalBlockStartTime n m - (r.val + 1))
  · intro r hr
    have hrData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp hr
    rw [canonicalPreBlockCarryCarrier_eq, mem_carryTwoPositions_iff]
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hrData.2⟩
  · intro a ha b hb hab
    have haData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp ha
    have hbData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp hb
    apply Fin.ext
    omega
  · intro i hi
    rw [canonicalPreBlockCarryCarrier_eq, mem_carryTwoPositions_iff] at hi
    have hiRange := Finset.mem_Ico.mp hi.1
    let r : Fin H := ⟨canonicalBlockStartTime n m - i - 1, by omega⟩
    refine ⟨r, ?_, ?_⟩
    · apply mem_canonicalPreBlockCarryTrueOffsets_iff.mpr
      refine ⟨by simp [r]; omega, ?_⟩
      have hsource : canonicalBlockStartTime n m -
          (canonicalBlockStartTime n m - i - 1 + 1) = i := by
        omega
      rw [hsource]
      exact hi.2
    · simp [r]
      omega

/-- A valid padded word bit is exactly the carry indicator at its represented
source. -/
theorem canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
    {n : OddNat} {H m : ℕ} {r : Fin H}
    (hvalid : r.val + 1 ≤ canonicalBlockStartTime n m) :
    (canonicalPreBlockCarryWord n H m r).toNat =
      canonicalCarryTwoIndicator n
        (canonicalBlockStartTime n m - (r.val + 1)) := by
  classical
  by_cases hcarry : CarryTwoDebtAt n
      (canonicalBlockStartTime n m - (r.val + 1))
  · simp [canonicalPreBlockCarryWord, canonicalCarryTwoIndicator,
      hvalid, hcarry]
  · simp [canonicalPreBlockCarryWord, canonicalCarryTwoIndicator,
      hvalid, hcarry]

/-! ## Direct recent-mass bridge -/

/-- In the mature regime, the signed recent carry mass is exactly the
cardinality of the finite pre-block carrier. -/
theorem canonicalRecentCarryMassBeforeStart_eq_preBlockCarryCarrier_card
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalRecentCarryMassBeforeStart n H m =
      (canonicalPreBlockCarryCarrier n H m).card := by
  classical
  rw [canonicalPreBlockCarryCarrier_eq]
  unfold canonicalRecentCarryMassBeforeStart canonicalCarryTwoIndicator
    carryTwoPositions
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : canonicalBlockStartTime n m -
      (canonicalBlockStartTime n m - H) = H := by
    omega
  rw [hlength, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro r hr
  have hrH : r < H := Finset.mem_range.mp hr
  have hsource : canonicalBlockStartTime n m - (H - 1 - r) - 1 =
      canonicalBlockStartTime n m - H + r := by
    omega
  rw [hsource]

/-- Mature recent mass is also the integer cast of the padded word's true-bit
count. -/
theorem canonicalRecentCarryMassBeforeStart_eq_wordTrueCount
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalRecentCarryMassBeforeStart n H m =
      canonicalPreBlockCarryWordTrueCount n H m := by
  rw [canonicalRecentCarryMassBeforeStart_eq_preBlockCarryCarrier_card hH,
    canonicalPreBlockCarryWordTrueCount_eq_carrier_card]

/-! ## Horizon-window coboundary -/

/-- Over every mature finite block window, positive-horizon frontier weight is
the horizon-zero weight plus only the recent-carry endpoint correction. -/
theorem canonicalSourceAgeFrontierWindowSum_eq_zero_add_recentCarryCoboundary
    {n : OddNat} {H q L : ℕ}
    (hH : H ≤ canonicalBlockStartTime n q) :
    canonicalSourceAgeFrontierWindowSum n H q L =
      canonicalSourceAgeFrontierWindowSum n 0 q L +
        canonicalRecentCarryMassBeforeStart n H q -
          canonicalRecentCarryMassBeforeStart n H (q + L) := by
  have hHend : H ≤ canonicalBlockStartTime n (q + L) :=
    hH.trans (canonicalBlockStartTime_mono n (by omega))
  rw [canonicalSourceAgeFrontierWindowSum_eq_deficit_sub,
    canonicalSourceAgeFrontierWindowSum_eq_deficit_sub,
    canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hH,
    canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hHend]
  ring

/-- Equality of the finite endpoint words implies equality of their true-bit
counts. -/
theorem canonicalPreBlockCarryWordTrueCount_eq_of_word_eq
    {n : OddNat} {H a b : ℕ}
    (hword : canonicalPreBlockCarryWord n H a =
      canonicalPreBlockCarryWord n H b) :
    canonicalPreBlockCarryWordTrueCount n H a =
      canonicalPreBlockCarryWordTrueCount n H b := by
  classical
  unfold canonicalPreBlockCarryWordTrueCount
    canonicalPreBlockCarryTrueOffsets
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hword]

/-- A mature window with equal recent carry words at both endpoints has the
same total weight at horizon `H` as at horizon zero. -/
theorem canonicalSourceAgeFrontierWindowSum_eq_zero_of_endpoint_words_eq
    {n : OddNat} {H q L : ℕ}
    (hH : H ≤ canonicalBlockStartTime n q)
    (hword : canonicalPreBlockCarryWord n H q =
      canonicalPreBlockCarryWord n H (q + L)) :
    canonicalSourceAgeFrontierWindowSum n H q L =
      canonicalSourceAgeFrontierWindowSum n 0 q L := by
  have hHend : H ≤ canonicalBlockStartTime n (q + L) :=
    hH.trans (canonicalBlockStartTime_mono n (by omega))
  have hmassStart := canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH
  have hmassEnd := canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hHend
  have hcount := canonicalPreBlockCarryWordTrueCount_eq_of_word_eq hword
  rw [canonicalSourceAgeFrontierWindowSum_eq_zero_add_recentCarryCoboundary hH]
  omega

/-! ## Fixed-horizon frontier boundedness audit

The positive-horizon correction is finite: at a mature block it is the
difference of two carry-word populations, each between `0` and `H`.  Hence a
fixed horizon cannot create or remove pointwise upper boundedness.  It only
changes a bound by a finite amount and changes finitely many initial blocks.

At horizon zero the exact reflected max normal form then reduces the audit to
the raw endpoint drift.  Thus the saturated and zero-drift branches are
already harmless (`1` and `0`, respectively); the unresolved arithmetic
content is precisely uniform upper boundedness of the positive-pressure
endpoint drift.  This section deliberately stops at that equivalence.  It
does not assume the desired queue or endpoint-width bound in order to prove
it. -/

/-- A padded carry word has at most `H` true bits. -/
theorem canonicalPreBlockCarryWordTrueCount_le
    (n : OddNat) (H m : ℕ) :
    canonicalPreBlockCarryWordTrueCount n H m ≤ H := by
  classical
  unfold canonicalPreBlockCarryWordTrueCount
    canonicalPreBlockCarryTrueOffsets
  calc
    (Finset.univ.filter fun r : Fin H =>
        canonicalPreBlockCarryWord n H m r = true).card ≤
        (Finset.univ : Finset (Fin H)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = H := by simp

/-- Mature recent carry mass is nonnegative. -/
theorem canonicalRecentCarryMassBeforeStart_nonneg
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    0 ≤ canonicalRecentCarryMassBeforeStart n H m := by
  rw [canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH]
  exact Int.natCast_nonneg _

/-- Mature recent carry mass is at most the fixed horizon. -/
theorem canonicalRecentCarryMassBeforeStart_le_horizon
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalRecentCarryMassBeforeStart n H m ≤ H := by
  rw [canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH]
  exact_mod_cast canonicalPreBlockCarryWordTrueCount_le n H m

/-- The block index is no larger than its source-time start. -/
theorem canonicalBlockIndex_le_startTime (n : OddNat) (m : ℕ) :
    m ≤ canonicalBlockStartTime n m := by
  have h := canonicalBlockStartTime_add_le_startTime_add n 0 m
  simp only [zero_add] at h
  omega

/-- On the mature tail, horizon `H` frontier weight is at most horizon-zero
weight plus `H`. -/
theorem canonicalSourceAgeFrontierIncrement_le_zero_add_horizon
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n H m ≤
      canonicalSourceAgeFrontierIncrement n 0 m + H := by
  have hHnext : H ≤ canonicalBlockStartTime n (m + 1) :=
    hH.trans (canonicalBlockStartTime_mono n (by omega))
  have hmassCurrent := canonicalRecentCarryMassBeforeStart_le_horizon hH
  have hmassNext := canonicalRecentCarryMassBeforeStart_nonneg hHnext
  rw [canonicalSourceAgeFrontierIncrement_eq_zero_add_recentCarryCoboundary hH]
  omega

/-- Conversely, horizon-zero frontier weight is at most horizon `H` weight
plus `H` on the mature tail. -/
theorem canonicalSourceAgeFrontierIncrement_zero_le_add_horizon
    {n : OddNat} {H m : ℕ}
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n 0 m ≤
      canonicalSourceAgeFrontierIncrement n H m + H := by
  have hHnext : H ≤ canonicalBlockStartTime n (m + 1) :=
    hH.trans (canonicalBlockStartTime_mono n (by omega))
  have hmassCurrent := canonicalRecentCarryMassBeforeStart_nonneg hH
  have hmassNext := canonicalRecentCarryMassBeforeStart_le_horizon hHnext
  rw [canonicalSourceAgeFrontierIncrement_eq_zero_add_recentCarryCoboundary hH]
  omega

/-- Every finite prefix of an integer sequence has an upper bound.  This
isolates the finite-origin correction used when passing from a mature-tail
bound to an all-block bound. -/
theorem exists_int_upperBound_before
    (f : ℕ → ℤ) (H : ℕ) :
    ∃ B : ℤ, ∀ m, m < H → f m ≤ B := by
  classical
  refine ⟨∑ i ∈ Finset.range H, |f i|, ?_⟩
  intro m hm
  calc
    f m ≤ |f m| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range H, |f i| := by
      exact Finset.single_le_sum
        (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hm)

/-- Uniform pointwise upper boundedness of the actual source-age frontier at
a fixed horizon. -/
def CanonicalSourceAgeFrontierIncrementUniformUpperBound
    (n : OddNat) (H : ℕ) : Prop :=
  ∃ B : ℤ, ∀ m,
    canonicalSourceAgeFrontierIncrement n H m ≤ B

/-- Fixed finite horizons all have the same pointwise upper-boundedness
status.  The carry coboundary changes the mature tail by at most `H`; the
remaining blocks form a finite prefix. -/
theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_zero
    (n : OddNat) (H : ℕ) :
    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
      CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0 := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨Bearly, hBearly⟩ := exists_int_upperBound_before
      (fun m => canonicalSourceAgeFrontierIncrement n 0 m) H
    refine ⟨max Bearly (B + H), ?_⟩
    intro m
    by_cases hm : m < H
    · exact (hBearly m hm).trans (le_max_left _ _)
    · have hH : H ≤ canonicalBlockStartTime n m := by
        exact (Nat.le_of_not_gt hm).trans (canonicalBlockIndex_le_startTime n m)
      have hcompare :=
        canonicalSourceAgeFrontierIncrement_zero_le_add_horizon hH
      have hmBound := hB m
      exact hcompare.trans (by omega)
  · rintro ⟨B, hB⟩
    obtain ⟨Bearly, hBearly⟩ := exists_int_upperBound_before
      (fun m => canonicalSourceAgeFrontierIncrement n H m) H
    refine ⟨max Bearly (B + H), ?_⟩
    intro m
    by_cases hm : m < H
    · exact (hBearly m hm).trans (le_max_left _ _)
    · have hH : H ≤ canonicalBlockStartTime n m := by
        exact (Nat.le_of_not_gt hm).trans (canonicalBlockIndex_le_startTime n m)
      have hcompare :=
        canonicalSourceAgeFrontierIncrement_le_zero_add_horizon hH
      have hmBound := hB m
      exact hcompare.trans (by omega)

/-- Uniform integer upper boundedness of the raw endpoint drift. -/
def CanonicalEndpointAccountingTermUniformUpperBound (n : OddNat) : Prop :=
  ∃ B : ℤ, ∀ m, endpointAccountingTerm n m ≤ B

/-- For a nonnegative ceiling, the exact horizon-zero reflected frontier is
bounded precisely when the raw endpoint drift is bounded by that ceiling. -/
theorem canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
    {n : OddNat} {m : ℕ} {B : ℤ} (hB : 0 ≤ B) :
    canonicalSourceAgeFrontierIncrement n 0 m ≤ B ↔
      endpointAccountingTerm n m ≤ B := by
  rw [canonicalSourceAgeFrontierIncrement_zero_eq_max, max_le_iff]
  constructor
  · exact fun h => h.2
  · intro hdrift
    exact ⟨by omega, hdrift⟩

/-- Horizon-zero frontier increments are uniformly bounded above exactly when
the raw endpoint drifts are.  Negative and zero drift are automatically
bounded; positive pressure is transmitted unchanged by the reflected max. -/
theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_zero_iff_endpoint
    (n : OddNat) :
    CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0 ↔
      CanonicalEndpointAccountingTermUniformUpperBound n := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, ?_⟩
    intro m
    have hfrontier : canonicalSourceAgeFrontierIncrement n 0 m ≤ max B 0 :=
      (hB m).trans (le_max_left _ _)
    exact (canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
      (n := n) (m := m) (B := max B 0) (le_max_right _ _)).mp hfrontier
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, ?_⟩
    intro m
    apply (canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
      (n := n) (m := m) (B := max B 0) (le_max_right _ _)).mpr
    exact (hB m).trans (le_max_left _ _)

/-- Final Stage-F audit: for every fixed horizon, pointwise frontier
boundedness is exactly the unresolved raw endpoint-drift boundedness problem.
No finite horizon can hide an unbounded positive-pressure family, and no such
family has been proved here. -/
theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint
    (n : OddNat) (H : ℕ) :
    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
      CanonicalEndpointAccountingTermUniformUpperBound n := by
  rw [canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_zero,
    canonicalSourceAgeFrontierIncrementUniformUpperBound_zero_iff_endpoint]

/-- For any proposed finite signature, existence of a sound projected
successor-edge upper table is equivalent to raw endpoint-drift boundedness.
Thus signature refinement can improve exact recovery or cycle visibility, but
cannot remove the Stage-F arithmetic obligation. -/
theorem exists_finiteSourceAgeProjectedUpperWeight_iff_endpoint
    {Signature : Type*} [Finite Signature]
    (n : OddNat) (H : ℕ) (signature : ℕ → Signature) :
    (∃ projectedUpperWeight : Signature → Signature → ℤ,
      FiniteSignatureSuccessorUpperWeightSound signature
        (canonicalSourceAgeFrontierIncrement n H) projectedUpperWeight) ↔
      CanonicalEndpointAccountingTermUniformUpperBound n := by
  rw [exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound]
  exact canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint n H

/-! ## Necessary pointwise bound for finite potentials -/

namespace CanonicalFiniteSourceAgeFrontierPotentialCertificate

variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]

/-- Every current finite-potential certificate forces a uniform upper bound on
each actual frontier increment.  The bound is the initial potential minus the
minimum potential on the finite signature type.

This is a necessary condition of this certificate method.  An arbitrary
signed flow may have uniformly nonpositive prefixes while retaining
unbounded positive individual increments, so prefix control alone does not
supply this pointwise condition. -/
theorem exists_frontierIncrement_uniformUpperBound
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate
      n H Signature) :
    ∃ B : ℤ, ∀ m,
      canonicalSourceAgeFrontierIncrement n H m ≤ B := by
  classical
  have huniv : (Finset.univ : Finset Signature).Nonempty :=
    ⟨F.certificate.signature 0, Finset.mem_univ _⟩
  obtain ⟨smin, _hsminMem, hsmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Signature)
      F.certificate.potential huniv
  refine ⟨F.certificate.potential (F.certificate.signature 0) -
      F.certificate.potential smin, ?_⟩
  intro m
  have hactual := F.certificate.actual_le_projected
    m (m + 1) (F.step_succ m)
  have hprojected := F.certificate.projected_le_potential_diff
    (F.certificate.signature m)
    (F.certificate.signature (m + 1))
  have hnext := F.potential_le_initial
    (F.certificate.signature (m + 1))
  have hcurrent := hsmin (F.certificate.signature m) (Finset.mem_univ _)
  rw [F.actualWeight_succ m] at hactual
  omega

/-- Every current finite source-age potential certificate already contains,
as a necessary consequence, the unresolved uniform endpoint-drift bound. -/
theorem to_endpointAccountingTermUniformUpperBound
    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate
      n H Signature) :
    CanonicalEndpointAccountingTermUniformUpperBound n := by
  apply (canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint
    n H).mp
  exact F.exists_frontierIncrement_uniformUpperBound

end CanonicalFiniteSourceAgeFrontierPotentialCertificate

/-! ## Horizon-one saturated-successor residual -/

/-- Successor demand after removing its final-source carry indicator.  This is
a signed scalar observable; it does not identify which queued source is later
consumed. -/
noncomputable def canonicalSaturatedSuccessorNonfinalDemand
    (n : OddNat) (m : ℕ) : ℤ :=
  canonicalQueueDemand n (m + 1) -
    canonicalCarryTwoIndicator n
      (canonicalBlockStartTime n (m + 2) - 1)

/-- Successor consumption after removing the one unit known to exist after a
saturated predecessor. -/
noncomputable def canonicalSaturatedSuccessorExtraConsumed
    (n : OddNat) (m : ℕ) : ℤ :=
  canonicalQueueConsumed n (m + 1) - 1

namespace CanonicalSaturatedBorderBlock

/-- The final-source indicator is one of the successor block's demand units. -/
theorem successor_finalIndicator_le_demand
    {n : OddNat} {m : ℕ} :
    canonicalCarryTwoIndicator n
        (canonicalBlockStartTime n (m + 2) - 1) ≤
      canonicalQueueDemand n (m + 1) := by
  have hfinal := card_erase_final_add_indicator_eq_blockClaimSourceCarrier
    n (m + 1)
  rw [card_canonicalBlockClaimSourceCarrier] at hfinal
  have hle : canonicalCarryTwoIndicator n
        (canonicalBlockStartTime n ((m + 1) + 1) - 1) ≤
      canonicalQueueDemand n (m + 1) := by
    omega
  simpa [show (m + 1) + 1 = m + 2 by omega] using hle

/-- A saturated predecessor guarantees at least one successor consumption
unit, so the extra-consumption residual is nonnegative. -/
theorem successorExtraConsumed_nonneg
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    0 ≤ canonicalSaturatedSuccessorExtraConsumed n m := by
  have hqueue : 1 ≤
      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
    rw [h.queueBeforeBlock_succ_eq_add_one]
    omega
  have havailable : 1 ≤
      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
        canonicalQueueDemand n (m + 1) := by omega
  have hservice : 1 ≤ canonicalQueueService n (m + 1) := by
    unfold canonicalQueueService
    rw [canonicalBlockCapacityCount_eq_terminalValuation]
    exact one_le_canonicalBlockTerminalValuation n (m + 1)
  have hconsumed : 1 ≤ canonicalQueueConsumed n (m + 1) := by
    unfold canonicalQueueConsumed
    exact le_min havailable hservice
  unfold canonicalSaturatedSuccessorExtraConsumed
  omega

/-- The nonfinal-demand residual is nonnegative because the removed indicator
is contained in successor demand. -/
theorem successorNonfinalDemand_nonneg
    {n : OddNat} {m : ℕ} :
    0 ≤ canonicalSaturatedSuccessorNonfinalDemand n m := by
  have hle := successor_finalIndicator_le_demand (n := n) (m := m)
  unfold canonicalSaturatedSuccessorNonfinalDemand
  omega

/-- Exact signed residual form of the horizon-one successor frontier.  This is
only scalar accounting.  It does not prove that the saturated block's named
final-source identity is itself the unit consumed by the successor. -/
theorem sourceAgeFrontierIncrement_one_succ_eq_nonfinalDemand_sub_extraConsumed
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalSourceAgeFrontierIncrement n 1 (m + 1) =
      canonicalSaturatedSuccessorNonfinalDemand n m -
        canonicalSaturatedSuccessorExtraConsumed n m := by
  rw [h.sourceAgeFrontierIncrement_one_succ_eq_boundary_balance]
  unfold canonicalSaturatedSuccessorNonfinalDemand
    canonicalSaturatedSuccessorExtraConsumed
  ring

/-! ## Saturated finite-word transition -/

/-- The newest bit before the successor of a saturated block is true: it is
the saturated block's final source. -/
theorem successor_extendedWord_head_eq_true
    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalPreBlockCarryWord n (H + 2) (m + 1)
      ⟨0, by omega⟩ = true := by
  classical
  have hstart : 1 ≤ canonicalBlockStartTime n (m + 1) := by
    rw [canonicalBlockStartTime_succ]
    have hlength := one_le_canonicalBlockLength n m
    omega
  have hendpointMem : paymentEndpointSeq n m ∈ canonicalPaymentBlock n m := by
    rw [canonicalPaymentBlock_eq_sourceFiber]
    exact endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)
  have hsource : canonicalBlockStartTime n (m + 1) - 1 =
      paymentEndpointSeq n m := by
    rw [canonicalBlockStartTime_succ]
    exact canonicalBlockStartTime_add_length_sub_one_eq_endpoint n m
  have hcarry : CarryTwoDebtAt n
      (canonicalBlockStartTime n (m + 1) - 1) := by
    rw [hsource]
    exact h.carryTwo_of_mem hendpointMem
  have hbit := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
    (n := n) (H := H + 2) (m := m + 1)
    (r := ⟨0, by omega⟩) hstart
  have hindicator := (canonicalCarryTwoIndicator_eq_one_iff n _).2 hcarry
  rw [hindicator] at hbit
  cases hword : canonicalPreBlockCarryWord n (H + 2) (m + 1)
      ⟨0, by omega⟩ <;> simp_all

/-- The second newest bit before the successor is also true: it is the start
source of the length-two saturated block. -/
theorem successor_extendedWord_second_eq_true
    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalPreBlockCarryWord n (H + 2) (m + 1)
      ⟨1, by omega⟩ = true := by
  classical
  have hnext : canonicalBlockStartTime n (m + 1) =
      canonicalBlockStartTime n m + 2 := by
    rw [canonicalBlockStartTime_succ, h.length_eq_two]
  have hvalid : 1 + 1 ≤ canonicalBlockStartTime n (m + 1) := by
    rw [hnext]
    omega
  have hstartMem : canonicalBlockStartTime n m ∈
      canonicalPaymentBlock n m := by
    rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart,
      ← canonicalBlockStartTime_eq_universalPaymentBlockStart]
    exact Finset.mem_Icc.mpr
      ⟨le_rfl, canonicalBlockStartTime_le_endpoint n m⟩
  have hsource : canonicalBlockStartTime n (m + 1) - (1 + 1) =
      canonicalBlockStartTime n m := by
    rw [hnext]
    omega
  have hcarry : CarryTwoDebtAt n
      (canonicalBlockStartTime n (m + 1) - (1 + 1)) := by
    rw [hsource]
    exact h.carryTwo_of_mem hstartMem
  have hbit := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
    (n := n) (H := H + 2) (m := m + 1)
    (r := ⟨1, by omega⟩) hvalid
  have hindicator := (canonicalCarryTwoIndicator_eq_one_iff n _).2 hcarry
  rw [hindicator] at hbit
  cases hword : canonicalPreBlockCarryWord n (H + 2) (m + 1)
      ⟨1, by omega⟩ <;> simp_all

/-- Beyond the two new saturated bits, the successor's extended word is the
old mature word shifted by exactly two positions. -/
theorem successor_extendedWord_tail_eq
    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hH : H ≤ canonicalBlockStartTime n m) (r : Fin H) :
    canonicalPreBlockCarryWord n (H + 2) (m + 1)
      ⟨r.val + 2, by omega⟩ =
        canonicalPreBlockCarryWord n H m r := by
  classical
  unfold canonicalPreBlockCarryWord
  have hnext : canonicalBlockStartTime n (m + 1) =
      canonicalBlockStartTime n m + 2 := by
    rw [canonicalBlockStartTime_succ, h.length_eq_two]
  have hvalidOld : r.val + 1 ≤ canonicalBlockStartTime n m := by
    omega
  have hvalidNew : r.val + 2 + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [hnext]
    omega
  have hsource : canonicalBlockStartTime n (m + 1) -
      (r.val + 2 + 1) =
        canonicalBlockStartTime n m - (r.val + 1) := by
    rw [hnext]
    omega
  simp [hvalidOld, hvalidNew, hsource]

/-- Every mature saturated frontier is read from the two crossing bits in the
successor's extended pre-block word.  The extension by two positions makes the
formula valid uniformly at `H = 0`, `H = 1`, and larger horizons. -/
theorem sourceAgeFrontierIncrement_eq_extendedWordBits
    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hH : H ≤ canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n H m =
      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
          ⟨H + 1, by omega⟩).toNat : ℤ) +
        (canonicalPreBlockCarryWord n (H + 2) (m + 1)
          ⟨H, by omega⟩).toNat - 1 := by
  rw [h.sourceAgeFrontierIncrement_eq_indicators hH]
  have hnext : canonicalBlockStartTime n (m + 1) =
      canonicalBlockStartTime n m + 2 := by
    rw [canonicalBlockStartTime_succ, h.length_eq_two]
  have hvalidLeft : H + 1 + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [hnext]
    omega
  have hvalidRight : H + 1 ≤
      canonicalBlockStartTime n (m + 1) := by
    rw [hnext]
    omega
  have hleft := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
    (n := n) (H := H + 2) (m := m + 1)
    (r := ⟨H + 1, by omega⟩) hvalidLeft
  have hright := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
    (n := n) (H := H + 2) (m := m + 1)
    (r := ⟨H, by omega⟩) hvalidRight
  have hsourceLeft : canonicalBlockStartTime n (m + 1) -
      (H + 1 + 1) = canonicalBlockStartTime n m - H := by
    rw [hnext]
    omega
  have hsourceRight : canonicalBlockStartTime n (m + 1) -
      (H + 1) = canonicalBlockStartTime n m - H + 1 := by
    rw [hnext]
    omega
  rw [hsourceLeft] at hleft
  rw [hsourceRight] at hright
  have hleftInt :
      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
        ⟨H + 1, by omega⟩).toNat : ℤ) =
          canonicalCarryTwoIndicator n
            (canonicalBlockStartTime n m - H) := by
    exact_mod_cast hleft
  have hrightInt :
      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
        ⟨H, by omega⟩).toNat : ℤ) =
          canonicalCarryTwoIndicator n
            (canonicalBlockStartTime n m - H + 1) := by
    exact_mod_cast hright
  rw [hleftInt, hrightInt]

/-- The extended-word formula recovers the known horizon-zero saturated
weight. -/
theorem sourceAgeFrontierIncrement_zero_eq_one_from_word
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalSourceAgeFrontierIncrement n 0 m = 1 :=
  h.sourceAgeFrontierIncrement_zero_eq_one

/-- The same finite-word update recovers exact horizon-one neutralization for
every mature saturated block. -/
theorem sourceAgeFrontierIncrement_one_eq_zero_from_word
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
    (hstart : 0 < canonicalBlockStartTime n m) :
    canonicalSourceAgeFrontierIncrement n 1 m = 0 :=
  h.sourceAgeFrontierIncrement_one_eq_zero hstart

end CanonicalSaturatedBorderBlock

/-! ## First finite frontier signature candidate

This signature records only noncircular, currently available finite
observables.  The queue coordinate uses `cap + 1` as an overflow marker; it
does not assert that the queue is bounded by `cap`.  The drift coordinate
records only sign, not the unbounded integer magnitude.  Therefore this is a
candidate projection, not yet a finite-potential certificate. -/

/-- Coarse local grammar class supplied by the exact endpoint-drift
trichotomy. -/
inductive CanonicalSourceAgeFrontierDriftClass where
  | negative
  | zero
  | positive
deriving DecidableEq

instance : Fintype CanonicalSourceAgeFrontierDriftClass where
  elems := {CanonicalSourceAgeFrontierDriftClass.negative,
    CanonicalSourceAgeFrontierDriftClass.zero,
    CanonicalSourceAgeFrontierDriftClass.positive}
  complete := by
    intro x
    cases x <;> simp

/-- First finite source-age frontier signature. -/
structure CanonicalSourceAgeFrontierSignature (H queueCap : ℕ) where
  carryWord : Fin H → Bool
  queueClass : Fin (queueCap + 2)
  driftClass : CanonicalSourceAgeFrontierDriftClass
  saturated : Bool
  finalCarry : Bool
deriving DecidableEq, Fintype

/-- Sign-only classification of the raw endpoint drift. -/
noncomputable def canonicalSourceAgeFrontierDriftClass
    (n : OddNat) (m : ℕ) : CanonicalSourceAgeFrontierDriftClass := by
  classical
  exact if endpointAccountingTerm n m < 0 then
    .negative
  else if endpointAccountingTerm n m = 0 then
    .zero
  else
    .positive

/-- The capped queue coordinate, with `queueCap + 1` representing every
larger queue.  This is an observation, not a queue-bound hypothesis. -/
noncomputable def canonicalSourceAgeFrontierQueueClass
    (n : OddNat) (queueCap m : ℕ) : Fin (queueCap + 2) :=
  ⟨min (canonicalOutstandingClaimQueueBeforeBlock n m) (queueCap + 1), by
    omega⟩

/-- Canonical realization of the first finite frontier signature. -/
noncomputable def canonicalSourceAgeFrontierSignature
    (n : OddNat) (H queueCap m : ℕ) :
    CanonicalSourceAgeFrontierSignature H queueCap := by
  classical
  exact
    { carryWord := canonicalPreBlockCarryWord n H m
      queueClass := canonicalSourceAgeFrontierQueueClass n queueCap m
      driftClass := canonicalSourceAgeFrontierDriftClass n m
      saturated := decide (CanonicalSaturatedBorderBlock n m)
      finalCarry := decide (CarryTwoDebtAt n
        (canonicalBlockStartTime n (m + 1) - 1)) }

/-- For the first concrete finite candidate, a sound projected upper table is
still equivalent to the global endpoint-drift bound.  The finite coordinates
do not manufacture the missing arithmetic ceiling. -/
theorem exists_candidateSourceAgeProjectedUpperWeight_iff_endpoint
    (n : OddNat) (H queueCap : ℕ) :
    (∃ projectedUpperWeight :
        CanonicalSourceAgeFrontierSignature H queueCap →
          CanonicalSourceAgeFrontierSignature H queueCap → ℤ,
      FiniteSignatureSuccessorUpperWeightSound
        (canonicalSourceAgeFrontierSignature n H queueCap)
        (canonicalSourceAgeFrontierIncrement n H)
        projectedUpperWeight) ↔
      CanonicalEndpointAccountingTermUniformUpperBound n :=
  exists_finiteSourceAgeProjectedUpperWeight_iff_endpoint
    n H (canonicalSourceAgeFrontierSignature n H queueCap)

end DkMath.Collatz
