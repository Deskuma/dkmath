/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.DriftBudget

#print "file: DkMath.Collatz.PetalBridge.PressureDecay"

namespace DkMath.Collatz


/-
This module is the first import-safe split from `PressureFrontier`.

It owns the generic pressure-depth balance vocabulary:

* integer margin and adjacent drops,
* net-drop balance identities,
* adjacent sign changes,
* pressure-margin jumps,
* local pulse predicates that do not mention frontiers or local islands.

Island-facing and frontier-facing bridge theorems stay in
`PressureFrontier`.  In particular, this file deliberately does not import
frontier/local-island predicates, so it can sit below `PressureFrontier`
without creating an import cycle.
-/

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
Integer-valued net pressure drop across adjacent pressure depths.

This is only a name for the balance quantity
`retention_drop - 2 * continuation_drop`.  Existing predicates keep their
current API, while later zero-crossing theorems can refer to this single
integer expression.
-/
noncomputable def SourcePressureNetDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceRetentionDropInt n k r j -
    2 * SourceContinuationDropInt n k r j

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
      SourcePressureNetDropInt n k r j := by
  unfold SourcePressureMarginInt
  unfold SourcePressureNetDropInt SourceRetentionDropInt SourceContinuationDropInt
  ring

/--
Next adjacent source-pressure margin as current margin plus net pressure drop.

This is the additive zero-crossing form of the checkpoint-136 balance sheet.
It is still local to one adjacent pressure-depth edge.
-/
theorem sourcePressureMargin_next_eq_current_add_netDrop
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j := by
  have h := sourcePressureMarginStepDiff_eq n k r j
  rw [← h]
  ring

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
Downward sign change of the source-pressure margin between adjacent depths.

This is the right-edge companion to `SourcePressureSignChangeUp`: the current
depth is positive, while the next adjacent pressure depth is nonpositive.
-/
def SourcePressureSignChangeDown
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j + 1) ≤ 0

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
Positive net integer drop across an adjacent pressure-depth edge.

This is intentionally not named `RetentionDropDominant` yet.  The predicate is
the algebraic quantity that actually appears in the margin-step identity:
retention loss minus twice continuation loss.
-/
def SourcePressureNetDropPositive
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureNetDropInt n k r j

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
Upward source-pressure sign change as a local zero-crossing.

The statement keeps the two axes separated: `j` is a pressure-depth edge, not a
time index.  The theorem says that the next margin is positive exactly when
the current nonpositive margin crosses zero after adding the local net pressure
drop.
-/
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeUp n k r j ↔
      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
        0 <
          SourcePressureMarginInt n k (r + j) +
            SourcePressureNetDropInt n k r j := by
  unfold SourcePressureSignChangeUp
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]

/--
Downward source-pressure sign change as a local falling condition.

This is the right-edge companion to
`sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses`: the current
positive margin falls to a nonpositive next margin after adding the local net
pressure drop.
-/
theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeDown n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + j) +
          SourcePressureNetDropInt n k r j ≤ 0 := by
  unfold SourcePressureSignChangeDown
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]

/--
Named local source-pressure pulse.

`SourcePressurePulse n k r j` records the two adjacent pressure-depth edges
around the selected depth `j`:

* the left edge crosses upward from a nonpositive margin after adding the
  local net pressure drop;
* the right edge falls from a positive margin to a nonpositive margin after
  adding the local net pressure drop.

This is deliberately still a local pressure-depth predicate.  It does not
claim that positive pressure depths form a prefix, an interval family, or a
global shape theorem.
-/
def SourcePressurePulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
    0 <
      SourcePressureMarginInt n k (r + (j - 1)) +
        SourcePressureNetDropInt n k r (j - 1)) ∧
    (0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0)

/--
Left-edge projection from a source-pressure pulse.
-/
theorem sourcePressurePulse_left
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressurePulse n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          SourcePressureNetDropInt n k r (j - 1) :=
  h.1

/--
Right-edge projection from a source-pressure pulse.
-/
theorem sourcePressurePulse_right
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressurePulse n k r j) :
    0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0 :=
  h.2

/--
Sign-change form of a local source-pressure pulse.

This alias keeps the sign-profile reading available beside the net-drop
reading in `SourcePressurePulse`.  It is useful when a later checkpoint wants
only the two signs, without opening the integer balance sheet.
-/
def SourcePressureSignPulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r (j - 1) ∧
    SourcePressureSignChangeDown n k r j

/--
The named net-drop pulse is equivalent to the two sign changes.
-/
theorem sourcePressurePulse_iff_signPulse
    (n : OddNat) (k r j : ℕ) :
    SourcePressurePulse n k r j ↔
      SourcePressureSignPulse n k r j := by
  unfold SourcePressurePulse SourcePressureSignPulse
  rw [sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses]
  rw [sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls]


end DkMath.Collatz
