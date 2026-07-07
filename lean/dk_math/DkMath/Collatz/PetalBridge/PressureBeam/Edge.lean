/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureBeam.Core

#print "file: DkMath.Collatz.PetalBridge.PressureBeam.Edge"

namespace DkMath.Collatz

/-
Beam crossing-edge target.

Checkpoint 221 separates two Beam-facing notions that cp220 showed should not
be conflated:

* `SourcePressureBeamDepthTarget n k r j` means the current depth `j` is already
  positive;
* `SourcePressureBeamCrossingEdgeTarget n k r j` means the edge `j -> j + 1`
  crosses from nonpositive to positive.

The crossing-edge target is intentionally a Beam-facing name for the existing
`SourcePressureSignChangeUp` predicate.  The new name is useful because the
left edge of an interval pulse is not a positive-depth target, but it is
exactly a crossing-edge target.  No propagation, coverage, or target transport
is introduced here.
-/

/--
Beam-facing target for an upward pressure crossing edge.

This is a vocabulary layer over `SourcePressureSignChangeUp`.  It is not a
positive-depth target: it records a boundary edge whose current margin is
nonpositive and whose next margin is positive.
-/
def SourcePressureBeamCrossingEdgeTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r j

/-- Crossing-edge targets expose nonpositive current margin. -/
theorem sourcePressureBeamCrossingEdgeTarget_current_nonpos
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
    SourcePressureMarginInt n k (r + j) ≤ 0 :=
  h.1

/-- Crossing-edge targets expose positive next margin. -/
theorem sourcePressureBeamCrossingEdgeTarget_next_pos
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) :=
  h.2

/--
A crossing-edge target cannot be a positive Beam depth target at its current
edge.

This is the API-level version of the cp220 obstruction: the left edge of a
crossing is a boundary before the positive run, not a positive selected depth.
-/
theorem not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
    ¬ SourcePressureBeamDepthTarget n k r j := by
  intro htarget
  have hpos := sourcePressureMargin_pos_of_beamDepthTarget n k r j htarget
  have hnonpos := sourcePressureBeamCrossingEdgeTarget_current_nonpos h
  omega

/--
The next-margin sign is algebraically equivalent to the named mass-balance
comparison at any edge.

Unlike the older addressed-target spelling, this theorem does not require a
positive current depth.  That is what the crossing-edge API needs: left
crossing edges are not Beam depth targets, but their next-margin positivity
still determines the same mass-balance inequality.
-/
theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
    (n : OddNat) (k r j : ℕ) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      SourcePressureBeamMassBalanceLeftInt n k r j <
        SourcePressureBeamMassBalanceRightInt n k r j := by
  unfold SourcePressureBeamMassBalanceLeftInt
  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
  omega

/--
Edge-local false/boundary mass-balance classifier without a positive-depth
target hypothesis.
-/
theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourcePressureBeamMassBalanceRightInt n k r j ≤
        SourcePressureBeamMassBalanceLeftInt n k r j := by
  unfold SourcePressureBeamMassBalanceLeftInt
  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
  omega

/--
Crossing-edge targets feed the True Beam mass-balance comparison at the same
edge without requiring `SourcePressureBeamAddressedDepthTarget`.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamCrossingEdgeTarget n k r j) :
    SourcePressureBeamMassBalanceLeftInt n k r j <
      SourcePressureBeamMassBalanceRightInt n k r j :=
  (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge n k r j).1
    (sourcePressureBeamCrossingEdgeTarget_next_pos h)

/--
An interval-pulse address supplies a Beam crossing-edge target at its exact
left edge.
-/
theorem sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamCrossingEdgeTarget n k r (A.start - 1) :=
  sourcePressureIntervalPulseAddress_left_signChange A

/--
The left edge of an interval-pulse address supplies the True Beam
mass-balance comparison through the crossing-edge target API.

This is the corrected cp221 replacement for trying to make the left edge into
`SourcePressureBeamAddressedDepthTarget`.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) :=
  sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
    (sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left A)

/--
A local-island witness supplies a Beam crossing-edge target at the left edge
of its generated singleton interval pulse.
-/
theorem sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureBeamCrossingEdgeTarget n k r
      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
  sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)

/--
A local-island witness supplies the True Beam mass-balance comparison at the
left edge of its generated singleton interval pulse.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
  sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
    (sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left W)

/-
Beam falling-edge target.

Checkpoint 222 completes the symmetric exact-edge vocabulary:

* `SourcePressureBeamCrossingEdgeTarget` reads an entrance edge
  `nonpositive -> positive`;
* `SourcePressureBeamFallingEdgeTarget` reads an exit edge
  `positive -> nonpositive`;
* `SourcePressureBeamDepthTarget` reads a positive current depth.

The falling-edge target is a Beam-facing name for the existing
`SourcePressureSignChangeDown` predicate.  It is useful because right-edge
false/boundary mass-balance comparisons can be read directly from the edge,
without requiring an addressed positive-depth target carrier.  This is still
only exact-edge vocabulary and algebra, not propagation or coverage.
-/

/--
Beam-facing target for a downward pressure falling edge.

This is a vocabulary layer over `SourcePressureSignChangeDown`: current margin
is positive and the next margin is nonpositive.
-/
def SourcePressureBeamFallingEdgeTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeDown n k r j

/-- Falling-edge targets expose positive current margin. -/
theorem sourcePressureBeamFallingEdgeTarget_current_pos
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
    0 < SourcePressureMarginInt n k (r + j) :=
  h.1

/-- Falling-edge targets expose nonpositive next margin. -/
theorem sourcePressureBeamFallingEdgeTarget_next_nonpos
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 :=
  h.2

/--
A falling-edge target is a positive Beam depth target at its current edge.

This is the main distinction from crossing edges: falling edges start inside a
positive run, so the current depth is selected.
-/
theorem sourcePressureBeamDepthTarget_of_fallingEdgeTarget
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
    SourcePressureBeamDepthTarget n k r j :=
  sourcePressureBeamDepthTarget_of_margin_pos n k r j
    (sourcePressureBeamFallingEdgeTarget_current_pos h)

/--
A crossing edge and a falling edge cannot occur at the same pressure edge.

They demand incompatible signs for the current margin.
-/
theorem not_crossingEdgeTarget_and_fallingEdgeTarget
    {n : OddNat} {k r j : ℕ}
    (hcross : SourcePressureBeamCrossingEdgeTarget n k r j) :
    ¬ SourcePressureBeamFallingEdgeTarget n k r j := by
  intro hfall
  have hnonpos := sourcePressureBeamCrossingEdgeTarget_current_nonpos hcross
  have hpos := sourcePressureBeamFallingEdgeTarget_current_pos hfall
  omega

/--
A falling-edge target feeds the False/Boundary Beam mass-balance comparison at
the same edge without requiring `SourcePressureBeamAddressedDepthTarget`.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
    {n : OddNat} {k r j : ℕ}
    (h : SourcePressureBeamFallingEdgeTarget n k r j) :
    SourcePressureBeamMassBalanceRightInt n k r j ≤
      SourcePressureBeamMassBalanceLeftInt n k r j :=
  (sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge n k r j).1
    (sourcePressureBeamFallingEdgeTarget_next_nonpos h)

/--
An interval-pulse address supplies a Beam falling-edge target at its exact
right edge.
-/
theorem sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamFallingEdgeTarget n k r (A.start + A.len - 1) :=
  sourcePressureIntervalPulseAddress_right_signChange A

/--
The right edge of an interval-pulse address supplies the False/Boundary
mass-balance comparison through the falling-edge target API.

Unlike the older right-edge theorem, this version does not require an
addressed-depth target hypothesis.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
      SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
  sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
    (sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right A)

/--
A local-island witness supplies a Beam falling-edge target at the right edge
of its generated singleton interval pulse.
-/
theorem sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureBeamFallingEdgeTarget n k r
      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
  sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)

/--
A local-island witness supplies the False/Boundary Beam comparison at the
right edge of its generated singleton interval pulse through the falling-edge
target API.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
      SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
  sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
    (sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right W)


end DkMath.Collatz
