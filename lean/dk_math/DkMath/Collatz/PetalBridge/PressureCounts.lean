/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureCore

#print "file: DkMath.Collatz.PetalBridge.PressureCounts"

namespace DkMath.Collatz


/-- Extract tail more-than-half pressure from a tail pressure profile. -/
theorem moreThanHalf_of_tailContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  h j hj

/--
Number of depths in `[r, r + len)` where source continuation has
more-than-half pressure.

This is a finite depth-mode count, not a window-mass count.
-/
noncomputable def sourceContinuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))

/--
Number of depths in `[r, r + len)` where tail continuation has
more-than-half pressure.
-/
noncomputable def tailContinuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
          (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))

/--
Number of depths in `[r, r + len)` where source continuation is controlled,
meaning it occupies at most half of source retention.
-/
noncomputable def sourceContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))

/--
Number of depths in `[r, r + len)` where tail continuation is controlled,
meaning it occupies at most half of tail retention.
-/
noncomputable def tailContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))

/-- Source pressure-depth count is bounded by the depth-range length. -/
theorem sourceContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationPressureDepthCount n k r len ≤ len := by
  classical
  unfold sourceContinuationPressureDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
      (l := List.range len))

/-- Tail pressure-depth count is bounded by the depth-range length. -/
theorem tailContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationPressureDepthCount n k r len ≤ len := by
  classical
  unfold tailContinuationPressureDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))
      (l := List.range len))

/-- Source controlled-depth count is bounded by the depth-range length. -/
theorem sourceContinuationControlledDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationControlledDepthCount n k r len ≤ len := by
  classical
  unfold sourceContinuationControlledDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
      (l := List.range len))

/-- Tail controlled-depth count is bounded by the depth-range length. -/
theorem tailContinuationControlledDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationControlledDepthCount n k r len ≤ len := by
  classical
  unfold tailContinuationControlledDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))
      (l := List.range len))

/--
The source depth range splits into controlled depths and pressure depths.
-/
theorem sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationControlledDepthCount n k r len +
      sourceContinuationPressureDepthCount n k r len = len := by
  classical
  unfold sourceContinuationControlledDepthCount
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0) +
            (if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0) = 1 := by
        by_cases hc :
            AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
              (orbitWindowRetentionMassPow2 n k (r + len))
        · have hnot :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hm
            unfold AtMostHalf at hc
            unfold MoreThanHalf at hm
            omega
          simp [hc, hnot]
        · have hm :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            cases
                atMostHalf_or_moreThanHalf
                  (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                  (orbitWindowRetentionMassPow2 n k (r + len)) with
            | inl hcontrolled => exact False.elim (hc hcontrolled)
            | inr hpressure => exact hpressure
          simp [hc, hm]
      omega

/--
The tail depth range splits into controlled depths and pressure depths.
-/
theorem tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationControlledDepthCount n k r len +
      tailContinuationPressureDepthCount n k r len = len := by
  classical
  unfold tailContinuationControlledDepthCount
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0) +
            (if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0) = 1 := by
        by_cases hc :
            AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
              (orbitWindowRetentionMassPow2Tail n k (r + len))
        · have hnot :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hm
            unfold AtMostHalf at hc
            unfold MoreThanHalf at hm
            omega
          simp [hc, hnot]
        · have hm :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            cases
                atMostHalf_or_moreThanHalf
                  (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                  (orbitWindowRetentionMassPow2Tail n k (r + len)) with
            | inl hcontrolled => exact False.elim (hc hcontrolled)
            | inr hpressure => exact hpressure
          simp [hc, hm]
      omega

/--
Source depth-frequency predicate: pressure occupies at most half of the depth
range.
-/
def SourcePressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len

/--
Source depth-frequency predicate: pressure occupies more than half of the depth
range.
-/
def SourcePressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len

/- Tail depth-frequency predicate: pressure occupies at most half of the depth
range. -/
def TailPressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationPressureDepthCount n k r len) len

/- Tail depth-frequency predicate: pressure occupies more than half of the
depth range. -/
def TailPressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationPressureDepthCount n k r len) len

/-- Source pressure frequency is either at most half or more than half. -/
theorem sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourcePressureAtMostHalfOnDepthRange n k r len ∨
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationPressureDepthCount n k r len) len

/-- Tail pressure frequency is either at most half or more than half. -/
theorem tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailPressureAtMostHalfOnDepthRange n k r len ∨
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationPressureDepthCount n k r len) len

/--
If source pressure is at most half of the depth range, then pressure depth
count is bounded by controlled depth count.
-/
theorem sourcePressureDepthCount_le_controlled_of_atMostHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureAtMostHalfOnDepthRange n k r len) :
    sourceContinuationPressureDepthCount n k r len ≤
      sourceContinuationControlledDepthCount n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange at h
  unfold AtMostHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source pressure depth count is bounded by controlled depth count, then
source pressure is at most half of the depth range.
-/
theorem sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationPressureDepthCount n k r len ≤
        sourceContinuationControlledDepthCount n k r len) :
    SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold AtMostHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
Tail pressure at most half implies tail pressure depth count is bounded by
tail controlled depth count.
-/
theorem tailPressureDepthCount_le_controlled_of_atMostHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailPressureAtMostHalfOnDepthRange n k r len) :
    tailContinuationPressureDepthCount n k r len ≤
      tailContinuationControlledDepthCount n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange at h
  unfold AtMostHalf at h
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail pressure depth count bounded by controlled count gives tail pressure at
most half. -/
theorem tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
    (n : OddNat) (k r len : ℕ)
    (h :
      tailContinuationPressureDepthCount n k r len ≤
        tailContinuationControlledDepthCount n k r len) :
    TailPressureAtMostHalfOnDepthRange n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange
  unfold AtMostHalf
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source pressure occupies more than half of the depth range, then controlled
depth count is strictly smaller than pressure depth count.
-/
theorem sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source controlled depth count is strictly smaller than pressure depth count,
then source pressure occupies more than half of the depth range.
-/
theorem sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange
  unfold MoreThanHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail more-than-half pressure implies tail controlled depth count is strictly
smaller than tail pressure depth count. -/
theorem tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailPressureMoreThanHalfOnDepthRange n k r len) :
    tailContinuationControlledDepthCount n k r len <
      tailContinuationPressureDepthCount n k r len := by
  unfold TailPressureMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail controlled depth count strictly below pressure depth count gives tail
more-than-half pressure. -/
theorem tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
    (n : OddNat) (k r len : ℕ)
    (h :
      tailContinuationControlledDepthCount n k r len <
        tailContinuationPressureDepthCount n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailPressureMoreThanHalfOnDepthRange
  unfold MoreThanHalf
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
Source more-than-half continuation pressure implies source continuation
outruns recovery.
-/
theorem continuationOutruns_of_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    ContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold ContinuationOutrunsRecovery
  rw [orbitWindowRetentionMass_split] at h
  omega

/--
Tail more-than-half continuation pressure implies tail continuation outruns
tail recovery.
-/
theorem tailContinuationOutruns_of_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold TailContinuationOutrunsRecovery
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega

/--
Number of depths in `[r, r + len)` where source continuation outruns recovery.

This is the cause-side failure count corresponding to source pressure depth
count.
-/
noncomputable def sourceContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (ContinuationOutrunsRecovery n k (r + j)))

/--
Number of depths in `[r, r + len)` where tail continuation outruns tail
recovery.
-/
noncomputable def tailContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailContinuationOutrunsRecovery n k (r + j)))

/-- Source outruns mode is equivalent to source more-than-half pressure. -/
theorem continuationOutruns_iff_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ) :
    ContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · exact moreThanHalf_continuation_of_continuationOutruns n k r
  · exact continuationOutruns_of_moreThanHalf_continuation n k r

/-- Tail outruns mode is equivalent to tail more-than-half pressure. -/
theorem tailContinuationOutruns_iff_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · exact moreThanHalf_tailContinuation_of_tailContinuationOutruns n k r
  · exact tailContinuationOutruns_of_moreThanHalf_tailContinuation n k r

/--
Source cause-side outruns count equals the source pressure depth count.
-/
theorem sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationOutrunsDepthCount n k r len =
      sourceContinuationPressureDepthCount n k r len := by
  classical
  unfold sourceContinuationOutrunsDepthCount
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (ContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
            if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            ContinuationOutrunsRecovery n k (r + len)
        · have hp :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (continuationOutruns_iff_moreThanHalf_continuation
              n k (r + len)).1 h
          simp [h, hp]
        · have hp :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hpressure
            exact h
              ((continuationOutruns_iff_moreThanHalf_continuation
                n k (r + len)).2 hpressure)
          simp [h, hp]
      rw [ih, hlast]

/--
Tail cause-side outruns count equals the tail pressure depth count.
-/
theorem tailContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailContinuationOutrunsDepthCount n k r len =
      tailContinuationPressureDepthCount n k r len := by
  classical
  unfold tailContinuationOutrunsDepthCount
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (TailContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
            if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            TailContinuationOutrunsRecovery n k (r + len)
        · have hp :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
            (tailContinuationOutruns_iff_moreThanHalf_tailContinuation
              n k (r + len)).1 h
          simp [h, hp]
        · have hp :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hpressure
            exact h
              ((tailContinuationOutruns_iff_moreThanHalf_tailContinuation
                n k (r + len)).2 hpressure)
          simp [h, hp]
      rw [ih, hlast]

/-- Source controlled mode implies source recovery dominance. -/
theorem recoveryDominates_of_atMostHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    RecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold RecoveryDominatesContinuation
  rw [orbitWindowRetentionMass_split] at h
  omega

/-- Tail controlled mode implies tail recovery dominance. -/
theorem tailRecoveryDominates_of_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailRecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold TailRecoveryDominatesContinuation
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega

/--
Number of depths in `[r, r + len)` where source recovery dominates
continuation.

This is the cause-side controlled count corresponding to source controlled
depth count.
-/
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (RecoveryDominatesContinuation n k (r + j)))

/--
Number of depths in `[r, r + len)` where tail recovery dominates tail
continuation.
-/
noncomputable def tailRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailRecoveryDominatesContinuation n k (r + j)))

/-- Source recovery dominance is equivalent to source controlled mode. -/
theorem recoveryDominates_iff_atMostHalf_continuation
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · intro h
    exact atMostHalf_continuation_of_continuation_le_recovery n k r h
  · exact recoveryDominates_of_atMostHalf_continuation n k r

/-- Tail recovery dominance is equivalent to tail controlled mode. -/
theorem tailRecoveryDominates_iff_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · intro h
    exact atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h
  · exact tailRecoveryDominates_of_atMostHalf_tailContinuation n k r

/--
Source cause-side dominance count equals the source controlled depth count.
-/
theorem sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len =
      sourceContinuationControlledDepthCount n k r len := by
  classical
  unfold sourceRecoveryDominanceDepthCount
  unfold sourceContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (RecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            RecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (recoveryDominates_iff_atMostHalf_continuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hcontrolled
            exact h
              ((recoveryDominates_iff_atMostHalf_continuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]

/--
Tail cause-side dominance count equals the tail controlled depth count.
-/
theorem tailRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len =
      tailContinuationControlledDepthCount n k r len := by
  classical
  unfold tailRecoveryDominanceDepthCount
  unfold tailContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (TailRecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            TailRecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
            (tailRecoveryDominates_iff_atMostHalf_tailContinuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hcontrolled
            exact h
              ((tailRecoveryDominates_iff_atMostHalf_tailContinuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]

/--
Cause-side source modes partition the depth range.
-/
theorem sourceCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len +
      sourceContinuationOutrunsDepthCount n k r len = len := by
  rw [sourceRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len

/--
Cause-side tail modes partition the depth range.
-/
theorem tailCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len +
      tailContinuationOutrunsDepthCount n k r len = len := by
  rw [tailRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len

/--
Cause-side source frequency predicate: source continuation outruns recovery in
at most half of the observed depth range.
-/
def SourceOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationOutrunsDepthCount n k r len) len

/--
Cause-side source frequency predicate: source continuation outruns recovery in
more than half of the observed depth range.
-/
def SourceOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationOutrunsDepthCount n k r len) len

/--
Cause-side tail frequency predicate: tail continuation outruns recovery in at
most half of the observed depth range.
-/
def TailOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationOutrunsDepthCount n k r len) len

/--
Cause-side tail frequency predicate: tail continuation outruns recovery in
more than half of the observed depth range.
-/
def TailOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationOutrunsDepthCount n k r len) len

/-- Source cause-side outruns frequency has the same dichotomy as pressure. -/
theorem sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ∨
      SourceOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationOutrunsDepthCount n k r len) len

/-- Tail cause-side outruns frequency has the same dichotomy as pressure. -/
theorem tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ∨
      TailOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationOutrunsDepthCount n k r len) len

/--
Source cause-side at-most-half frequency is equivalent to descriptive source
pressure at-most-half frequency.
-/
theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
      SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourcePressureAtMostHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Source cause-side more-than-half frequency is equivalent to descriptive source
pressure more-than-half frequency.
-/
theorem sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsMoreThanHalfOnDepthRange n k r len ↔
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Tail cause-side at-most-half frequency is equivalent to descriptive tail
pressure at-most-half frequency.
-/
theorem tailOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ↔
      TailPressureAtMostHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailPressureAtMostHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Tail cause-side more-than-half frequency is equivalent to descriptive tail
pressure more-than-half frequency.
-/
theorem tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsMoreThanHalfOnDepthRange n k r len ↔
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
If source outruns depths occupy more than half of the depth range, then they
strictly outnumber source dominance depths.
-/
theorem sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceRecoveryDominanceDepthCount n k r len <
      sourceContinuationOutrunsDepthCount n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If tail outruns depths occupy more than half of the depth range, then they
strictly outnumber tail dominance depths.
-/
theorem tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailRecoveryDominanceDepthCount n k r len <
      tailContinuationOutrunsDepthCount n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
  omega

/--
Source cause-side outruns-heavy frequency gives descriptive source pressure
heavy frequency.
-/
theorem sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len :=
  (sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h

/--
Tail cause-side outruns-heavy frequency gives descriptive tail pressure heavy
frequency.
-/
theorem tailPressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len :=
  (tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h

/--
Source cause-side outruns-heavy frequency forces descriptive pressure depths to
outnumber controlled depths.
-/
theorem sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len :=
  sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    n k r len
    (sourcePressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)

/--
Tail cause-side outruns-heavy frequency forces descriptive pressure depths to
outnumber controlled depths.
-/
theorem tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailContinuationControlledDepthCount n k r len <
      tailContinuationPressureDepthCount n k r len :=
  tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    n k r len
    (tailPressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)

/--
Source cause-side outruns-heavy frequency guarantees that at least one source
pressure depth exists.
-/
theorem sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < sourceContinuationPressureDepthCount n k r len := by
  have hlt :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len :=
    sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega

/--
Tail cause-side outruns-heavy frequency guarantees that at least one tail
pressure depth exists.
-/
theorem tailPressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < tailContinuationPressureDepthCount n k r len := by
  have hlt :
      tailContinuationControlledDepthCount n k r len <
        tailContinuationPressureDepthCount n k r len :=
    tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega

/--
If the source outruns side does not fill a nonempty range, then the source
dominance side is present.

This is a small partition-consumption lemma for later recovery-side arguments.
-/
theorem sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
    (n : OddNat) (k r len : ℕ)
    (_h : SourceOutrunsAtMostHalfOnDepthRange n k r len)
    (hnotAllOutruns :
      sourceContinuationOutrunsDepthCount n k r len < len) :
    0 < sourceRecoveryDominanceDepthCount n k r len := by
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If the tail outruns side does not fill a nonempty range, then the tail
dominance side is present.

This is the shifted-tail counterpart of the source partition-consumption lemma.
-/
theorem tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
    (n : OddNat) (k r len : ℕ)
    (_h : TailOutrunsAtMostHalfOnDepthRange n k r len)
    (hnotAllOutruns :
      tailContinuationOutrunsDepthCount n k r len < len) :
    0 < tailRecoveryDominanceDepthCount n k r len := by
  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If source continuation pressure holds at every depth of the range, then the
source pressure-depth count fills the whole range.
-/
theorem sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
    (n : OddNat) (k r len : ℕ)
    (h : SourceContinuationPressureOnRange n k r len) :
    sourceContinuationPressureDepthCount n k r len = len := by
  classical
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      have ih' :
          (List.range len).countP
              (fun j =>
                decide
                  (MoreThanHalf
                    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                    (orbitWindowRetentionMassPow2 n k (r + j)))) = len := by
        apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
      have hlast :
          decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len))) = true := by
        exact decide_eq_true (h len (Nat.lt_succ_self len))
      rw [ih', hlast]
      simp

/--
If tail continuation pressure holds at every depth of the range, then the tail
pressure-depth count fills the whole range.
-/
theorem tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
    (n : OddNat) (k r len : ℕ)
    (h : TailContinuationPressureOnRange n k r len) :
    tailContinuationPressureDepthCount n k r len = len := by
  classical
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      have ih' :
          (List.range len).countP
              (fun j =>
                decide
                  (MoreThanHalf
                    (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
                    (orbitWindowRetentionMassPow2Tail n k (r + j)))) = len := by
        apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
      have hlast :
          decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len))) = true := by
        exact decide_eq_true (h len (Nat.lt_succ_self len))
      rw [ih', hlast]
      simp

/--
Predicate-facing source half criterion.

This is the readable version of
`atMostHalf_continuation_of_continuation_le_recovery`.
-/
theorem atMostHalf_continuation_of_recoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : RecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_continuation_le_recovery n k r h

/-- Predicate-facing tail half criterion. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : TailRecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) :=
  atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h

/-- Predicate-facing source half criterion from recovery budget coverage. -/
theorem atMostHalf_continuation_of_recoveryCoversHalf
    (n : OddNat) (k r : ℕ)
    (h : RecoveryCoversHalfRetention n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_retention_le_two_recovery n k r h

/-- Predicate-facing tail half criterion from tail recovery budget coverage. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
    (n : OddNat) (k r : ℕ)
    (h : TailRecoveryCoversHalfRetention n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) :=
  atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery n k r h

/-- A range dominance hypothesis yields the source half criterion at each depth. -/
theorem atMostHalf_continuation_of_recoveryDominatesOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : RecoveryDominatesOnRange n k r len) (hj : j < len) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  atMostHalf_continuation_of_recoveryDominates n k (r + j) (h j hj)

/-- A tail range dominance hypothesis yields the tail half criterion at each depth. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailRecoveryDominatesOnRange n k r len) (hj : j < len) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  atMostHalf_tailContinuation_of_tailRecoveryDominates n k (r + j) (h j hj)


end DkMath.Collatz
