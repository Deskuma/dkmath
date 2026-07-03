/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.DriftBudget

#print "file: DkMath.Collatz.PetalBridge.PressureFrontier"

namespace DkMath.Collatz


/--
More-than-half pressure at depth `2` forces positive depth-two continuation
mass.

This is the first thin entrance from the pressure vocabulary into the delayed
reservoir budget.
-/
theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
    (n : OddNat) (k : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 := by
  unfold MoreThanHalf at h
  omega

/--
Meaning-name wrapper for extracting local source pressure from a finite source
pressure profile.

Use this theorem at call sites instead of the more generic internal extractor
when the proof is conceptually moving from range pressure to a local depth.
-/
theorem sourcePressureAtDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  moreThanHalf_of_sourceContinuationPressure n k r len j h hj

/--
Local source pressure at any depth forces positive source continuation mass at
that depth.
-/
theorem sourceContinuationMass_pos_of_localPressure
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold MoreThanHalf at h
  omega

/--
Range pressure yields positive source continuation mass at any selected depth
inside the range.
-/
theorem sourceContinuationMass_pos_of_pressureOnRange_at
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  sourceContinuationMass_pos_of_localPressure n k (r + j)
    (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)

/--
A selected source pressure depth inside a depth range.

This predicate packages the local `MoreThanHalf` statement so later accounting
lemmas can talk about selected depths without repeating the mass expressions.
-/
def IsSourcePressureDepth
    (n : OddNat) (k r : ℕ) (j : ℕ) : Prop :=
  MoreThanHalf
    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
    (orbitWindowRetentionMassPow2 n k (r + j))

/--
Integer-valued source pressure margin at a single depth.

The margin is positive exactly when source continuation occupies more than
half of source retention.  It is intentionally integer-valued, because the
natural-number subtraction would truncate negative margins and hide failures.
-/
noncomputable def SourcePressureMarginInt
    (n : OddNat) (k r : ℕ) : ℤ :=
  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
    (orbitWindowRetentionMassPow2 n k r : ℤ)

/--
Integer-valued retention drop across adjacent pressure depths.

The sign convention is `current - next`.  This is the convention used by the
Python pressure scan and by the checkpoint-136 balance sheet.  Keeping it as
an integer avoids truncation when a later experiment crosses a non-monotone
edge.
-/
noncomputable def SourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)

/--
Integer-valued continuation drop across adjacent pressure depths.

This uses the same `current - next` convention as `SourceRetentionDropInt`.
The continuation term appears with coefficient `2` in the source pressure
margin, so the net pressure contribution is
`retention_drop - 2 * continuation_drop`.
-/
noncomputable def SourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

/--
Adjacent source-pressure margin accounting identity.

This is the checkpoint-136 balance sheet.  A positive pressure step is exactly
the net effect of losing retention mass faster than twice the continuation
mass across the same adjacent pressure-depth edge.  No global pressure-prefix
or dominance theorem is asserted here.
-/
theorem sourcePressureMarginStepDiff_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) -
        SourcePressureMarginInt n k (r + j) =
      SourceRetentionDropInt n k r j -
        2 * SourceContinuationDropInt n k r j := by
  unfold SourcePressureMarginInt
  unfold SourceRetentionDropInt SourceContinuationDropInt
  ring

/--
Selected source pressure is exactly positive source pressure margin.

This theorem is the safe algebraic bridge for later prefix/frontier work:
pressure-prefix questions can be studied as margin-positivity questions.
-/
theorem isSourcePressureDepth_iff_margin_pos
    (n : OddNat) (k r j : ℕ) :
    IsSourcePressureDepth n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) := by
  unfold IsSourcePressureDepth SourcePressureMarginInt MoreThanHalf
  omega

/--
A finite selected source-pressure prefix.

`SelectedPressurePrefix n k r len m` says that the first `m` depth indices in
the range beginning at `r` are selected.  The `m ≤ len` field keeps this
predicate tied to the finite observation range used by pressure-depth counts.
-/
def SelectedPressurePrefix
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m ≤ len ∧
    ∀ j, j < m → IsSourcePressureDepth n k r j

/--
Witness that source-pressure selection is not prefix-shaped at the given
window.

This is a diagnostic predicate, not a contradiction.  It records the situation

```text
shallow depth j₁ is not selected,
deeper depth j₂ is selected.
```

The point of naming this obstruction is to prevent future work from assuming
that pressure behaves like nested carrier membership.  Carrier membership is
nested; the pressure margin `2 * continuation - retention` can change sign in
a non-prefix pattern.
-/
def SourcePressurePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    ¬ IsSourcePressureDepth n k r j₁ ∧
    IsSourcePressureDepth n k r j₂

/-- Extract the shallow/deep order from a source-pressure prefix failure. -/
theorem sourcePressurePrefixFailure_lt
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    j₁ < j₂ :=
  h.1

/-- The shallow side of a source-pressure prefix failure is not selected. -/
theorem not_isSourcePressureDepth_of_prefixFailure_left
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    ¬ IsSourcePressureDepth n k r j₁ :=
  h.2.1

/-- The deeper side of a source-pressure prefix failure is selected. -/
theorem isSourcePressureDepth_of_prefixFailure_right
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    IsSourcePressureDepth n k r j₂ :=
  h.2.2

/--
Source-pressure prefix failure is exactly the margin sign pattern
`nonpositive -> positive`.

This is the preferred algebraic form for later experiments: Python can report
the integer margins, while Lean keeps the logical predicate and the margin
predicate equivalent.
-/
theorem sourcePressurePrefixFailure_iff_margin
    (n : OddNat) (k r j₁ j₂ : ℕ) :
    SourcePressurePrefixFailure n k r j₁ j₂ ↔
      j₁ < j₂ ∧
        SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + j₂) := by
  constructor
  · intro h
    have hleft :
        SourcePressureMarginInt n k (r + j₁) ≤ 0 := by
      have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + j₁) := by
        intro hpos
        exact h.2.1 ((isSourcePressureDepth_iff_margin_pos n k r j₁).2 hpos)
      omega
    have hright :
        0 < SourcePressureMarginInt n k (r + j₂) :=
      (isSourcePressureDepth_iff_margin_pos n k r j₂).1 h.2.2
    exact ⟨h.1, hleft, hright⟩
  · intro h
    have hleft :
        ¬ IsSourcePressureDepth n k r j₁ := by
      intro hsel
      have hpos :
          0 < SourcePressureMarginInt n k (r + j₁) :=
        (isSourcePressureDepth_iff_margin_pos n k r j₁).1 hsel
      omega
    have hright :
        IsSourcePressureDepth n k r j₂ :=
      (isSourcePressureDepth_iff_margin_pos n k r j₂).2 h.2.2
    exact ⟨h.1, hleft, hright⟩

/--
A prefix failure inside the proposed prefix length refutes the selected-prefix
predicate.

The deeper selected witness is part of the failure data even though the proof
only needs the shallow non-selection plus `j₁ < j₂ < m`.
-/
theorem not_selectedPressurePrefix_of_prefixFailure
    (n : OddNat) (k r len m j₁ j₂ : ℕ)
    (hfail : SourcePressurePrefixFailure n k r j₁ j₂)
    (hj₂ : j₂ < m)
    (_hm : m ≤ len) :
    ¬ SelectedPressurePrefix n k r len m := by
  intro hprefix
  have hj₁ : j₁ < m := Nat.lt_trans hfail.1 hj₂
  exact hfail.2.1 (hprefix.2 j₁ hj₁)

/--
Down-closed source-pressure selected set below `m`.

This is weaker and safer than an unconditional prefix theorem: it states that
if a deeper selected depth appears below `m`, then all shallower depths below
it are selected too.
-/
def SourcePressureSelectedSetDownClosed
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∀ j₁ j₂,
    j₁ < j₂ →
    j₂ < m →
    IsSourcePressureDepth n k r j₂ →
      IsSourcePressureDepth n k r j₁

/--
Down-closed selected depths are equivalent to having no prefix-failure witness
below `m`.

This gives future code a clean choice: prove down-closedness by excluding
failures, or produce a failure as a precise obstruction.
-/
theorem downClosed_iff_no_prefixFailure
    (n : OddNat) (k r m : ℕ) :
    SourcePressureSelectedSetDownClosed n k r m ↔
      ∀ j₁ j₂,
        j₁ < j₂ →
        j₂ < m →
        ¬ SourcePressurePrefixFailure n k r j₁ j₂ := by
  constructor
  · intro hclosed j₁ j₂ hlt hj₂ hfail
    exact hfail.2.1 (hclosed j₁ j₂ hlt hj₂ hfail.2.2)
  · intro hno j₁ j₂ hlt hj₂ hdeep
    classical
    by_cases hshallow : IsSourcePressureDepth n k r j₁
    · exact hshallow
    · exact False.elim (hno j₁ j₂ hlt hj₂ ⟨hlt, hshallow, hdeep⟩)

/--
Upward sign change of the source-pressure margin between adjacent depths.

This is a small building block for pressure-frontier and pressure-island
classification.  It is stated directly in margin language because the
checkpoint-125 correction is that pressure should be studied as a sign profile,
not as raw carrier membership.
-/
def SourcePressureSignChangeUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + j + 1)

/--
Named pressure-margin jump between adjacent pressure depths.

Checkpoint 134 starts the thin `PressureDecayProfile` vocabulary here rather
than introducing a full grid.  The predicate only compares adjacent pressure
depths `r + j` and `r + j + 1`; it says nothing about time indices and does
not assert that selected pressure depths form a prefix.
-/
def SourcePressureMarginJumpUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) <
    SourcePressureMarginInt n k (r + j + 1)

/--
Retention mass strictly drops across adjacent pressure depths.

This is intentionally a comparison predicate instead of a natural-number
subtraction.  The experimental scan reports numeric drops, but the Lean API
keeps the first pressure-decay layer order-theoretic.
-/
def SourceRetentionDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  orbitWindowRetentionMassPow2 n k (r + j + 1) <
    orbitWindowRetentionMassPow2 n k (r + j)

/--
Continuation mass weakly drops across adjacent pressure depths.

The weak form is the safe default for checkpoint 134: it records monotone
decay across the adjacent pressure depths without claiming a quantitative
dominance relation.
-/
def SourceContinuationWeaklyDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) ≤
    orbitWindowContinuationSiblingMassPow2 n k (r + j)

/--
Observed pressure jump equipped with a strict retention drop.

The name deliberately avoids "dominant": dominance in the Python scan uses
the quantitative inequality `retention_drop > 2 * continuation_drop`, which is
not part of this thin Lean predicate yet.
-/
def SourcePressureJumpWithRetentionDrop
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j

/--
Observed pressure jump with both retention and continuation decay information.

Checkpoint 135 keeps this as a thin packaging predicate.  It still avoids any
quantitative dominance claim; it only records that the margin jumps upward,
retention strictly drops, and continuation weakly drops across the same
adjacent pressure-depth edge.
-/
def SourcePressureJumpWithDecay
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j ∧
      SourceContinuationWeaklyDropsAcross n k r j

/--
Positive net integer drop across an adjacent pressure-depth edge.

This is intentionally not named `RetentionDropDominant` yet.  The predicate is
the algebraic quantity that actually appears in the margin-step identity:
retention loss minus twice continuation loss.
-/
def SourcePressureNetDropPositive
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 <
    SourceRetentionDropInt n k r j -
      2 * SourceContinuationDropInt n k r j

/--
The first selected source-pressure depth.

This is a frontier, not a prefix theorem.  It says that `j` is selected and all
shallower depths are not selected.  Later work can decide whether the selected
set continues, stops, or forms an island after this frontier.
-/
def SourcePressureFrontier
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j ∧
    ∀ i, i < j → ¬ IsSourcePressureDepth n k r i

/--
Frontier in margin language.

The first selected depth is exactly the first positive source-pressure margin.
-/
theorem sourcePressureFrontier_iff_margin
    (n : OddNat) (k r j : ℕ) :
    SourcePressureFrontier n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) ∧
        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
  constructor
  · intro h
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 h.1
    · intro i hi
      have hnot := h.2 i hi
      have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + i) := by
        intro hpos
        exact hnot ((isSourcePressureDepth_iff_margin_pos n k r i).2 hpos)
      omega
  · intro h
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 h.1
    · intro i hi hsel
      have hpos :
          0 < SourcePressureMarginInt n k (r + i) :=
        (isSourcePressureDepth_iff_margin_pos n k r i).1 hsel
      have hle := h.2 i hi
      omega

/--
A positive frontier after depth `0` produces a concrete prefix-failure witness.

This is the bridge from the frontier reading back to the checkpoint-125
obstruction predicate.
-/
theorem sourcePressurePrefixFailure_of_frontier_pos
    (n : OddNat) (k r j : ℕ)
    (hfront : SourcePressureFrontier n k r j)
    (hj : 0 < j) :
    SourcePressurePrefixFailure n k r 0 j := by
  constructor
  · exact hj
  · constructor
    · exact hfront.2 0 hj
    · exact hfront.1

/--
A positive frontier produces an upward sign change at the previous depth.

This is a local margin view of
`sourcePressurePrefixFailure_of_frontier_pos`.
-/
theorem sourcePressureSignChangeUp_of_frontier_pos
    (n : OddNat) (k r j : ℕ)
    (hfront : SourcePressureFrontier n k r j)
    (hj : 0 < j) :
    SourcePressureSignChangeUp n k r (j - 1) := by
  unfold SourcePressureSignChangeUp
  have hprev_not : ¬ IsSourcePressureDepth n k r (j - 1) := by
    exact hfront.2 (j - 1) (Nat.sub_lt hj Nat.zero_lt_one)
  have hprev_nonpos :
      SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 := by
    have hnotpos :
        ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
      intro hpos
      exact hprev_not
        ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
    omega
  have hj_pos :
      0 < SourcePressureMarginInt n k (r + j) :=
    (isSourcePressureDepth_iff_margin_pos n k r j).1 hfront.1
  constructor
  · exact hprev_nonpos
  · have hidx : r + (j - 1) + 1 = r + j := by omega
    simpa [hidx] using hj_pos

/--
Local isolated positive source-pressure depth.

This is deliberately only a predicate.  Margin equivalences and count theorems
should be added after numerical scans show which island shapes actually matter.
-/
def SourcePressureLocalIsland
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < j ∧
    IsSourcePressureDepth n k r j ∧
    ¬ IsSourcePressureDepth n k r (j - 1) ∧
    ¬ IsSourcePressureDepth n k r (j + 1)

/--
Local pressure island in margin language.

This is the first theorem interface for isolated positive pressure depths.
-/
theorem sourcePressureLocalIsland_iff_margin
    (n : OddNat) (k r j : ℕ) :
    SourcePressureLocalIsland n k r j ↔
      0 < j ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
  constructor
  · intro h
    rcases h with ⟨hj, hsel, hprev_not, hnext_not⟩
    constructor
    · exact hj
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
    constructor
    · have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
        intro hpos
        exact hprev_not
          ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
      omega
    · have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + (j + 1)) := by
        intro hpos
        exact hnext_not
          ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
      omega
  · intro h
    rcases h with ⟨hj, hpos, hprev_nonpos, hnext_nonpos⟩
    constructor
    · exact hj
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 hpos
    constructor
    · intro hprev
      have hp :
          0 < SourcePressureMarginInt n k (r + (j - 1)) :=
        (isSourcePressureDepth_iff_margin_pos n k r (j - 1)).1 hprev
      omega
    · intro hnext
      have hp :
          0 < SourcePressureMarginInt n k (r + (j + 1)) :=
        (isSourcePressureDepth_iff_margin_pos n k r (j + 1)).1 hnext
      omega

/--
A consecutive block of positive source-pressure depths.

Checkpoint 130 keeps this predicate intentionally thin.  The Python
pressure-sign scan shows that positive depths often appear as blocks, while
local islands can also occur.  This predicate records only the block condition;
it does not assert maximality, uniqueness, or prefix behavior.
-/
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j

/--
Positive pressure block in margin language.
-/
theorem sourcePressurePositiveBlock_iff_margin
    (n : OddNat) (k r a len : ℕ) :
    SourcePressurePositiveBlock n k r a len ↔
      0 < len ∧
        ∀ j, a ≤ j → j < a + len →
          0 < SourcePressureMarginInt n k (r + j) := by
  unfold SourcePressurePositiveBlock
  constructor
  · intro h
    constructor
    · exact h.1
    · intro j hle hlt
      exact (isSourcePressureDepth_iff_margin_pos n k r j).1
        (h.2 j hle hlt)
  · intro h
    constructor
    · exact h.1
    · intro j hle hlt
      exact (isSourcePressureDepth_iff_margin_pos n k r j).2
        (h.2 j hle hlt)

/--
A selected source-pressure depth is a positive block of length one.
-/
theorem sourcePressurePositiveBlock_singleton
    (n : OddNat) (k r j : ℕ)
    (h : IsSourcePressureDepth n k r j) :
    SourcePressurePositiveBlock n k r j 1 := by
  constructor
  · omega
  · intro t hle hlt
    have ht : t = j := by omega
    simpa [ht] using h

/--
Build a positive source-pressure block from positive margins on the interval.
-/
theorem sourcePressurePositiveBlock_of_forall_margin_pos
    (n : OddNat) (k r a len : ℕ)
    (hlen : 0 < len)
    (hpos : ∀ j, a ≤ j → j < a + len →
      0 < SourcePressureMarginInt n k (r + j)) :
    SourcePressurePositiveBlock n k r a len :=
  (sourcePressurePositiveBlock_iff_margin n k r a len).2 ⟨hlen, hpos⟩

/--
There is a local source-pressure island below a finite depth bound.
-/
def ExistsSourcePressureLocalIslandBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureLocalIsland n k r j

/--
Existence of a bounded local pressure island in margin language.
-/
theorem existsSourcePressureLocalIslandBelow_iff_margin
    (n : OddNat) (k r m : ℕ) :
    ExistsSourcePressureLocalIslandBelow n k r m ↔
      ∃ j, j < m ∧
        0 < j ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
  unfold ExistsSourcePressureLocalIslandBelow
  constructor
  · intro h
    rcases h with ⟨j, hjm, hjisland⟩
    rw [sourcePressureLocalIsland_iff_margin] at hjisland
    exact ⟨j, hjm, hjisland⟩
  · intro h
    rcases h with ⟨j, hjm, hjmargin⟩
    exact ⟨j, hjm, (sourcePressureLocalIsland_iff_margin n k r j).2 hjmargin⟩

/--
Build bounded local-island existence from an explicit bounded island witness.
-/
theorem existsSourcePressureLocalIslandBelow_of_lt
    (n : OddNat) (k r m j : ℕ)
    (hjm : j < m)
    (hisland : SourcePressureLocalIsland n k r j) :
    ExistsSourcePressureLocalIslandBelow n k r m :=
  ⟨j, hjm, hisland⟩

/--
There is a source-pressure frontier below a finite depth bound.
-/
def ExistsSourcePressureFrontierBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureFrontier n k r j

/--
Existence of a bounded pressure frontier in margin language.
-/
theorem existsSourcePressureFrontierBelow_iff_margin
    (n : OddNat) (k r m : ℕ) :
    ExistsSourcePressureFrontierBelow n k r m ↔
      ∃ j, j < m ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
  unfold ExistsSourcePressureFrontierBelow
  constructor
  · intro h
    rcases h with ⟨j, hjm, hfront⟩
    rw [sourcePressureFrontier_iff_margin] at hfront
    exact ⟨j, hjm, hfront⟩
  · intro h
    rcases h with ⟨j, hjm, hmargin⟩
    exact ⟨j, hjm, (sourcePressureFrontier_iff_margin n k r j).2 hmargin⟩

/--
Build bounded frontier existence from an explicit bounded frontier witness.
-/
theorem existsSourcePressureFrontierBelow_of_lt
    (n : OddNat) (k r m j : ℕ)
    (hjm : j < m)
    (hfront : SourcePressureFrontier n k r j) :
    ExistsSourcePressureFrontierBelow n k r m :=
  ⟨j, hjm, hfront⟩

/--
An upward pressure sign change strictly increases the integer pressure margin.
-/
theorem sourcePressureMargin_lt_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginInt n k (r + j) <
      SourcePressureMarginInt n k (r + j + 1) := by
  rcases h with ⟨hle, hpos⟩
  omega

/--
An upward sign change is a named pressure-margin jump.
-/
theorem sourcePressureMarginJumpUp_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginJumpUp n k r j :=
  sourcePressureMargin_lt_of_signChangeUp n k r j h

/--
A local pressure island produces an upward sign change at its left edge.
-/
theorem sourcePressureSignChangeUp_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureSignChangeUp n k r (j - 1) := by
  rcases hisland with ⟨hjpos, hsel, hprev_not, _hnext_not⟩
  unfold SourcePressureSignChangeUp
  constructor
  · have hnotpos :
        ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
      intro hpos
      exact hprev_not
        ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
    omega
  · have hpos :
        0 < SourcePressureMarginInt n k (r + j) :=
      (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
    have hidx : r + (j - 1) + 1 = r + j := by omega
    simpa [hidx] using hpos

/--
A local pressure island gives a strict margin jump at its left edge.

Checkpoint 133 reads local islands as pressure-depth decay imbalance witnesses.
This theorem is still margin-only: it does not yet choose a retention or
continuation drop decomposition, but it gives the exact interface that such a
future `PressureDecayProfile` should refine.
-/
theorem sourcePressureMargin_lt_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) <
      SourcePressureMarginInt n k (r + (j - 1) + 1) :=
  sourcePressureMargin_lt_of_signChangeUp n k r (j - 1)
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

/--
A local pressure island gives a named pressure-margin jump at its left edge.

This is the checkpoint-134 vocabulary version of
`sourcePressureMargin_lt_of_localIsland_left`.
-/
theorem sourcePressureMarginJumpUp_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginJumpUp n k r (j - 1) :=
  sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

/--
Strict adjacent margin jump is equivalent to positive integer step
difference.
-/
theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      0 <
        SourcePressureMarginInt n k (r + j + 1) -
          SourcePressureMarginInt n k (r + j) := by
  unfold SourcePressureMarginJumpUp
  omega

/--
Positive net retention/continuation drop forces a named pressure-margin jump.

This is the first Lean use of the checkpoint-136 balance sheet.  It remains a
local adjacent-edge theorem; it does not claim any global prefix shape for
selected pressure depths.
-/
theorem sourcePressureMarginJumpUp_of_netDropPositive
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureNetDropPositive n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
  unfold SourcePressureNetDropPositive at h
  rw [sourcePressureMarginStepDiff_eq]
  exact h

/--
A named pressure-margin jump gives positive net integer pressure drop.

Together with `sourcePressureMarginJumpUp_of_netDropPositive`, this closes the
local checkpoint-137 equivalence between adjacent margin jumps and the integer
balance sheet.  This remains strictly local to one adjacent pressure-depth
edge.
-/
theorem sourcePressureNetDropPositive_of_marginJumpUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureMarginJumpUp n k r j) :
    SourcePressureNetDropPositive n k r j := by
  unfold SourcePressureNetDropPositive
  rw [← sourcePressureMarginStepDiff_eq]
  exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h

/--
Adjacent pressure-margin jump is exactly positive net pressure drop.

This theorem is the stable local API for later pressure-decay work.  It should
be preferred over introducing a global or dominance-sounding predicate until a
specific downstream theorem requires that stronger vocabulary.
-/
theorem sourcePressureMarginJumpUp_iff_netDropPositive
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      SourcePressureNetDropPositive n k r j :=
  ⟨sourcePressureNetDropPositive_of_marginJumpUp n k r j,
    sourcePressureMarginJumpUp_of_netDropPositive n k r j⟩

/--
An upward pressure sign change has positive net integer pressure drop.
-/
theorem sourcePressureNetDropPositive_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureNetDropPositive n k r j :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r j
    (sourcePressureMarginJumpUp_of_signChangeUp n k r j h)

/--
A local pressure island has positive net integer pressure drop at its left
edge.
-/
theorem sourcePressureNetDropPositive_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureNetDropPositive n k r (j - 1) :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)

/--
Package a named margin jump and a strict retention drop.

This checkpoint-135 wrapper is deliberately non-quantitative: it does not say
that the retention drop dominates the continuation drop.  It only records that
both observations are attached to the same adjacent pressure-depth edge.
-/
theorem sourcePressureJumpWithRetentionDrop_of_parts
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j :=
  ⟨hjump, hret⟩

/--
An upward sign change plus a strict retention drop packages as a
pressure-jump-with-retention-drop witness.
-/
theorem sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hchange : SourcePressureSignChangeUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j :=
  sourcePressureJumpWithRetentionDrop_of_parts n k r j
    (sourcePressureMarginJumpUp_of_signChangeUp n k r j hchange) hret

/--
A local pressure island left edge plus a strict retention drop packages as a
pressure-jump-with-retention-drop witness.
-/
theorem sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j)
    (hret : SourceRetentionDropsAcross n k r (j - 1)) :
    SourcePressureJumpWithRetentionDrop n k r (j - 1) :=
  sourcePressureJumpWithRetentionDrop_of_parts n k r (j - 1)
    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland) hret

/--
Package the three thin pressure-decay observations for the same edge.

This is the source-code signpost for the next refinement: once integer drop
amounts are introduced, this predicate should be the order-theoretic input
side of the identity
`margin_next - margin_current = retention_drop - 2 * continuation_drop`.
-/
theorem sourcePressureJumpWithDecay_of_parts
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j :=
  ⟨hjump, hret, hcont⟩

/--
An upward sign change plus retention/continuation decay packages as a
pressure-jump-with-decay witness.
-/
theorem sourcePressureJumpWithDecay_of_signChangeUp_of_decay
    (n : OddNat) (k r j : ℕ)
    (hchange : SourcePressureSignChangeUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j :=
  sourcePressureJumpWithDecay_of_parts n k r j
    (sourcePressureMarginJumpUp_of_signChangeUp n k r j hchange) hret hcont

/--
Positive net pressure drop plus the two order-theoretic decay observations
packages as `SourcePressureJumpWithDecay`.
-/
theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
    (n : OddNat) (k r j : ℕ)
    (hnet : SourcePressureNetDropPositive n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j :=
  sourcePressureJumpWithDecay_of_parts n k r j
    (sourcePressureMarginJumpUp_of_netDropPositive n k r j hnet) hret hcont

/-- The empty selected-pressure prefix is always available. -/
theorem selectedPressurePrefix_zero
    (n : OddNat) (k r len : ℕ) :
    SelectedPressurePrefix n k r len 0 := by
  unfold SelectedPressurePrefix
  constructor
  · omega
  · intro j hj
    omega

/-- Extract the range bound from a selected-pressure prefix. -/
theorem selectedPressurePrefix_le_len
    {n : OddNat} {k r len m : ℕ}
    (h : SelectedPressurePrefix n k r len m) :
    m ≤ len :=
  h.1

/-- Extract a selected depth from a selected-pressure prefix. -/
theorem isSourcePressureDepth_of_selectedPressurePrefix
    {n : OddNat} {k r len m j : ℕ}
    (h : SelectedPressurePrefix n k r len m)
    (hj : j < m) :
    IsSourcePressureDepth n k r j :=
  h.2 j hj

/--
A full pressure profile over `[r, r + len)` supplies every shorter selected
pressure prefix.
-/
theorem selectedPressurePrefix_of_pressureOnRange
    (n : OddNat) (k r len m : ℕ)
    (hm : m ≤ len)
    (h : SourceContinuationPressureOnRange n k r len) :
    SelectedPressurePrefix n k r len m := by
  unfold SelectedPressurePrefix
  constructor
  · exact hm
  · intro j hj
    unfold IsSourcePressureDepth
    exact h j (by omega)

/-- Range pressure marks every in-range depth as a selected source pressure depth. -/
theorem isSourcePressureDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    IsSourcePressureDepth n k r j := by
  unfold IsSourcePressureDepth
  exact sourcePressureAtDepth_of_pressureOnRange n k r len j h hj

/-- A selected source pressure depth has positive source continuation mass. -/
theorem positive_sourceContinuationMass_of_isSourcePressureDepth
    (n : OddNat) (k r j : ℕ)
    (h : IsSourcePressureDepth n k r j) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  unfold IsSourcePressureDepth at h
  exact sourceContinuationMass_pos_of_localPressure n k (r + j) h

/--
Positive source pressure-depth count selects at least one local pressure depth.

This is intentionally only an existence theorem.  It does not claim that
multiple selected depths are independent.
-/
theorem exists_sourcePressureDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j)) := by
  classical
  unfold sourceContinuationPressureDepthCount at hpos
  induction len with
  | zero =>
      simp at hpos
  | succ len ih =>
      rw [List.range_succ] at hpos
      by_cases hlast :
          MoreThanHalf
            (orbitWindowContinuationSiblingMassPow2 n k (r + len))
            (orbitWindowRetentionMassPow2 n k (r + len))
      · exact ⟨len, by omega, hlast⟩
      · have hprev :
            0 <
              (List.range len).countP
                (fun j =>
                  decide
                    (MoreThanHalf
                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                      (orbitWindowRetentionMassPow2 n k (r + j)))) := by
          simpa [hlast] using hpos
        rcases ih hprev with ⟨j, hj, hpressure⟩
        exact ⟨j, by omega, hpressure⟩

/--
Positive source pressure-depth count selects a depth with positive source
continuation mass.
-/
theorem exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩

/-- Positive pressure-depth count selects a packaged pressure-depth witness. -/
theorem exists_isSourcePressureDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧ IsSourcePressureDepth n k r j := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, hpressure⟩

/--
Positive pressure-depth count selects a packaged pressure-depth witness together
with its positive source continuation mass.
-/
theorem exists_isSourcePressureDepth_with_positive_mass
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      IsSourcePressureDepth n k r j ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_isSourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, hpressure,
    positive_sourceContinuationMass_of_isSourcePressureDepth n k r j hpressure⟩

/--
Two selected source pressure depths exist when the pressure-depth count is at
least two.

This theorem only extracts distinct witnesses.  It intentionally does not say
that their delayed-budget contributions are independent.
-/
theorem exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
    (n : OddNat) (k r len : ℕ)
    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
    ∃ j₁ j₂,
      j₁ < len ∧
      j₂ < len ∧
      j₁ ≠ j₂ ∧
      IsSourcePressureDepth n k r j₁ ∧
      IsSourcePressureDepth n k r j₂ := by
  classical
  unfold sourceContinuationPressureDepthCount at hcount
  induction len with
  | zero =>
      simp at hcount
  | succ len ih =>
      rw [List.range_succ] at hcount
      by_cases hlast : IsSourcePressureDepth n k r len
      · have hlast' :
            MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
              (orbitWindowRetentionMassPow2 n k (r + len)) := by
          simpa [IsSourcePressureDepth] using hlast
        by_cases hprevpos :
            0 <
              (List.range len).countP
                (fun j =>
                  decide
                    (MoreThanHalf
                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                      (orbitWindowRetentionMassPow2 n k (r + j))))
        · rcases exists_isSourcePressureDepth_of_pressureDepthCount_pos
            n k r len hprevpos with ⟨j, hj, hpressure⟩
          exact ⟨j, len, by omega, by omega, by omega, hpressure, hlast⟩
        · have hprevzero :
              (List.range len).countP
                (fun j =>
                  decide
                    (MoreThanHalf
                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                      (orbitWindowRetentionMassPow2 n k (r + j)))) = 0 :=
            Nat.eq_zero_of_not_pos hprevpos
          simp [hlast', hprevzero] at hcount
      · have hlast' :
            ¬ MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
              (orbitWindowRetentionMassPow2 n k (r + len)) := by
          intro h
          exact hlast (by simpa [IsSourcePressureDepth] using h)
        have hprev :
            2 ≤
              (List.range len).countP
                (fun j =>
                  decide
                    (MoreThanHalf
                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                      (orbitWindowRetentionMassPow2 n k (r + j)))) := by
          simpa [hlast'] using hcount
        rcases ih hprev with ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩
        exact ⟨j₁, j₂, by omega, by omega, hne, hp₁, hp₂⟩

/--
Unpack the two-witness theorem into the original `MoreThanHalf` spelling.

This theorem is useful for callers that do not yet use the packaged predicate.
-/
theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
    (n : OddNat) (k r len : ℕ)
    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
    ∃ j₁ j₂,
      j₁ < len ∧
      j₂ < len ∧
      j₁ ≠ j₂ ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j₁))
        (orbitWindowRetentionMassPow2 n k (r + j₁)) ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j₂))
        (orbitWindowRetentionMassPow2 n k (r + j₂)) := by
  rcases exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
    n k r len hcount with ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩
  exact ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩

/--
Source cause-side outruns-heavy pressure yields a concrete positive source
continuation mass at some selected depth.
-/
theorem exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  have hpos :
      0 < sourceContinuationPressureDepthCount n k r len :=
    sourcePressureDepthCount_pos_of_outrunsMoreThanHalf n k r len h
  exact exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos

/--
Tower-entry naming wrapper for positive pressure-depth count.

The theorem only selects a positive local source continuation mass.  It does
not assert that different selected depths are independent budget carriers.
-/
theorem exists_towerEntryDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos

/--
Tower-entry naming wrapper for source outruns-heavy pressure.

This is the caller-facing name for moving from a pressure-heavy range to one
selected local tower-entry opportunity.
-/
theorem exists_towerEntryDepth_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf n k r len h

/--
Extract local depth-two source pressure from the one-depth range pressure
profile beginning at depth `2`.
-/
theorem sourcePressureDepthTwo_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k 2)
      (orbitWindowRetentionMassPow2 n k 2) := by
  simpa using moreThanHalf_of_sourceContinuationPressure n k 2 1 0 h (by omega)

/--
One-depth range pressure at depth `2` forces positive depth-two continuation
mass.
-/
theorem sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 :=
  sourceContinuationMass_depth_two_pos_of_pressure_depth_two n k
    (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)

/--
Pressure-facing wrapper for the depth-two delayed-reservoir budget.

The pressure hypothesis is not needed by the inequality itself; it records the
intended caller context, where a pressure-heavy depth supplies positive
continuation mass and then uses the delayed budget.
-/
theorem sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
    (n : OddNat) (k : ℕ)
    (_h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k :=
  sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder n k

/--
Depth-two one-range pressure gives both positive continuation mass and the
depth-two delayed budget inequality.

This is the first direct "selected witness to delayed budget" bridge.
-/
theorem depthTwoPressureRange_positive_and_budget
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        sumS n ((k + 1) + 1) +
          orbitWindowResidueCountMod8EqSevenTail n k := by
  constructor
  · exact sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one n k h
  · exact sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder n k
      (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)

/--
Alias spelling for the same depth-two bridge, emphasizing existence of a
budget opportunity rather than the pressure-profile input form.
-/
theorem exists_depth_two_budget_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        sumS n ((k + 1) + 1) +
          orbitWindowResidueCountMod8EqSevenTail n k :=
  depthTwoPressureRange_positive_and_budget n k h

/--
Depth-two delayed budget predicate.

This packages the positive mass and delayed-budget inequality as a reusable
property for later multi-witness accounting experiments.
-/
def HasDepthTwoDelayedBudget
    (n : OddNat) (k : ℕ) : Prop :=
  0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k

/-- Depth-two one-range pressure supplies a packaged delayed budget. -/
theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    HasDepthTwoDelayedBudget n k := by
  unfold HasDepthTwoDelayedBudget
  exact depthTwoPressureRange_positive_and_budget n k h


end DkMath.Collatz
