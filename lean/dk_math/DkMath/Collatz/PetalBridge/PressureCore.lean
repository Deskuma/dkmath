/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Mass

#print "file: DkMath.Collatz.PetalBridge.PressureCore"

namespace DkMath.Collatz


/--
If source continuation mass is no larger than source recovery mass, then source
continuation occupies at most half of the parent retention mass.
-/
theorem atMostHalf_continuation_of_continuation_le_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2 n k r ≤
        orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split]
  omega

/--
If tail continuation mass is no larger than tail recovery mass, then tail
continuation occupies at most half of tail retention mass.
-/
theorem atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2Tail n k r ≤
        orbitWindowRecoverySiblingMassPow2Tail n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/--
If source recovery accounts for at least half of source retention, then source
continuation is at most half of source retention.
-/
theorem atMostHalf_continuation_of_retention_le_two_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowRetentionMassPow2 n k r ≤
        2 * orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split] at h ⊢
  omega

/--
If tail recovery accounts for at least half of tail retention, then tail
continuation is at most half of tail retention.
-/
theorem atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowRetentionMassPow2Tail n k r ≤
        2 * orbitWindowRecoverySiblingMassPow2Tail n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMassPow2Tail_split] at h ⊢
  omega

/-- Source continuation mass is at most the whole source retention mass. -/
theorem continuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2_le_retentionMass n k r

/-- Tail continuation mass is at most the whole tail retention mass. -/
theorem tailContinuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail n k r

/-- Source recovery mass is at most the whole source retention mass. -/
theorem recovery_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowRecoverySiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowRecoverySiblingMassPow2_le_retentionMass n k r

/-- Tail recovery mass is at most the whole tail retention mass. -/
theorem tailRecovery_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowRecoverySiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail n k r

/--
Source comparison predicate: recovery mass dominates continuation mass.

This names the local comparison condition that is sufficient for the source
`AtMostHalf` criterion.  It is intentionally a hypothesis package, not an
unconditional theorem.
-/
def RecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2 n k r ≤
    orbitWindowRecoverySiblingMassPow2 n k r

/--
Tail comparison predicate: tail recovery mass dominates tail continuation mass.
-/
def TailRecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2Tail n k r ≤
    orbitWindowRecoverySiblingMassPow2Tail n k r

/--
Source budget predicate: recovery covers at least half of retention.

This is often the natural form when a later argument produces a lower bound on
recovery rather than a direct comparison with continuation.
-/
def RecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2 n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2 n k r

/-- Tail budget predicate: tail recovery covers at least half of tail retention. -/
def TailRecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2Tail n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2Tail n k r

/--
Finite-depth range form of source recovery dominance.

This keeps the persistent-comparison hypothesis explicit without proving it.
-/
def RecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → RecoveryDominatesContinuation n k (r + j)

/-- Finite-depth range form of tail recovery dominance. -/
def TailRecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → TailRecoveryDominatesContinuation n k (r + j)

/--
Failure-mode predicate: source continuation strictly outruns recovery.

This is the obstruction-facing complement direction to
`RecoveryDominatesContinuation`.
-/
def ContinuationOutrunsRecovery
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRecoverySiblingMassPow2 n k r <
    orbitWindowContinuationSiblingMassPow2 n k r

/-- Tail failure-mode predicate: tail continuation strictly outruns tail recovery. -/
def TailContinuationOutrunsRecovery
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRecoverySiblingMassPow2Tail n k r <
    orbitWindowContinuationSiblingMassPow2Tail n k r

/-- Finite-depth range form of source continuation outrunning recovery. -/
def ContinuationOutrunsRecoveryOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → ContinuationOutrunsRecovery n k (r + j)

/-- Finite-depth range form of tail continuation outrunning recovery. -/
def TailContinuationOutrunsRecoveryOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → TailContinuationOutrunsRecovery n k (r + j)

/-- Each source depth is either recovery-dominant or continuation-outrunning. -/
theorem recoveryDominates_or_continuationOutruns
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ∨
      ContinuationOutrunsRecovery n k r := by
  unfold RecoveryDominatesContinuation ContinuationOutrunsRecovery
  omega

/-- Each tail depth is either recovery-dominant or continuation-outrunning. -/
theorem tailRecoveryDominates_or_tailContinuationOutruns
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ∨
      TailContinuationOutrunsRecovery n k r := by
  unfold TailRecoveryDominatesContinuation TailContinuationOutrunsRecovery
  omega

/-- Source continuation outrunning recovery rules out recovery dominance. -/
theorem not_recoveryDominates_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    ¬ RecoveryDominatesContinuation n k r := by
  intro hdom
  unfold ContinuationOutrunsRecovery at h
  unfold RecoveryDominatesContinuation at hdom
  omega

/-- Tail continuation outrunning recovery rules out tail recovery dominance. -/
theorem not_tailRecoveryDominates_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    ¬ TailRecoveryDominatesContinuation n k r := by
  intro hdom
  unfold TailContinuationOutrunsRecovery at h
  unfold TailRecoveryDominatesContinuation at hdom
  omega

/-- Extract a source failure observation from a finite-depth failure range. -/
theorem continuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    ContinuationOutrunsRecovery n k (r + j) :=
  h j hj

/-- Extract a tail failure observation from a finite-depth failure range. -/
theorem tailContinuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    TailContinuationOutrunsRecovery n k (r + j) :=
  h j hj

/--
If source continuation outruns recovery, then source continuation occupies more
than half of the parent retention mass.
-/
theorem moreThanHalf_continuation_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold MoreThanHalf
  unfold ContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMass_split]
  omega

/--
If tail continuation outruns tail recovery, then tail continuation occupies
more than half of tail retention mass.
-/
theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold MoreThanHalf
  unfold TailContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/-- A source failure range gives more-than-half pressure at each depth. -/
theorem moreThanHalf_continuation_of_outRunsOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  moreThanHalf_continuation_of_continuationOutruns
    n k (r + j) (continuationOutrunsRecovery_of_onRange n k r len j h hj)

/-- A tail failure range gives more-than-half pressure at each depth. -/
theorem moreThanHalf_tailContinuation_of_outRunsOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  moreThanHalf_tailContinuation_of_tailContinuationOutruns
    n k (r + j) (tailContinuationOutrunsRecovery_of_onRange n k r len j h hj)

/--
Generic finite range profile for strict more-than-half pressure.

The functions `count` and `total` are indexed by depth.  The predicate says
that every depth in the interval `[r, r + len)` carries `MoreThanHalf` pressure.
-/
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))

/--
Source continuation pressure profile over a finite depth range.

This packages the statement that source continuation occupies more than half
of source retention at every depth in `[r, r + len)`.
-/
def SourceContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
    (fun d => orbitWindowRetentionMassPow2 n k d)
    r len

/--
Tail continuation pressure profile over a finite depth range.

This is the shifted-tail counterpart of
`SourceContinuationPressureOnRange`.
-/
def TailContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
    (fun d => orbitWindowRetentionMassPow2Tail n k d)
    r len

/-- A source failure range promotes to a source continuation pressure profile. -/
theorem sourceContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len) :
    SourceContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_continuation_of_outRunsOnRange n k r len j h hj

/-- A tail failure range promotes to a tail continuation pressure profile. -/
theorem tailContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len) :
    TailContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_tailContinuation_of_outRunsOnRange n k r len j h hj

/-- Extract source more-than-half pressure from a source pressure profile. -/
theorem moreThanHalf_of_sourceContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  h j hj


end DkMath.Collatz
