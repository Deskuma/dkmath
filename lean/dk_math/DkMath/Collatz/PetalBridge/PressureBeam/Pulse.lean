/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureBeam.Edge

#print "file: DkMath.Collatz.PetalBridge.PressureBeam.Pulse"

namespace DkMath.Collatz

/-
Local pulse-shape packaging.

Checkpoint 223 keeps this as theorem packaging rather than a new predicate.
The three target vocabularies are already precise enough:

* entry edge: `SourcePressureBeamCrossingEdgeTarget`;
* active selected depth: `SourcePressureBeamAddressedDepthTarget`;
* exit edge: `SourcePressureBeamFallingEdgeTarget`.

The paired interval theorem records only the exact two boundary edges of one
given pulse address.  The witness theorem adds the addressed-depth target at
the singleton pulse's right/center edge, and that part necessarily requires
`W ∈ L`: addressed targets are list-relative carriers, while crossing/falling
edge targets are intrinsic sign-change facts of the witness-generated pulse.

This section deliberately does not claim interior coverage, family coverage,
canonical target selection, overlap repair, or Collatz convergence.
-/

/--
An interval-pulse address packages its two exact Beam boundary edges.

The left edge is the entrance crossing at `A.start - 1`; the right edge is the
falling exit at `A.start + A.len - 1`.
-/
theorem sourcePressureBeamPulse_edges_of_intervalPulseAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamCrossingEdgeTarget n k r (A.start - 1) ∧
      SourcePressureBeamFallingEdgeTarget n k r (A.start + A.len - 1) :=
  ⟨sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left A,
    sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right A⟩

/--
An interval-pulse address packages the entry and exit mass-balance comparisons.

This is the finite local pulse shape:
entry gives the True Beam comparison `left < right`, while exit gives the
False/Boundary comparison `right <= left`.
-/
theorem sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
        SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) ∧
      SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
        SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
  ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing A,
    sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling A⟩

/--
A local-island witness packages the singleton pulse shape:

* crossing target at the generated pulse's left edge;
* addressed positive depth at the generated pulse's right/center edge;
* falling target at the same generated pulse's right edge.

The addressed-depth component is list-relative, hence the `W ∈ L` hypothesis.
-/
theorem sourcePressureBeamPulse_witness_singleton_shape
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamCrossingEdgeTarget n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
      SourcePressureBeamAddressedDepthTarget L
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
        SourcePressureBeamFallingEdgeTarget n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
  ⟨sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left W,
    sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem,
    sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right W⟩

/--
A local-island witness packages the singleton pulse's two edge comparisons:
True Beam at entry and False/Boundary at exit.
-/
theorem sourcePressureBeamPulse_witness_singleton_massBalance_edges
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
        SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
      SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
        SourcePressureBeamMassBalanceLeftInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
  ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left W,
    sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling W⟩

/-
Diagnostic-facing consumers of the local pulse-shape package.

Checkpoint 224 inspected the downstream obstruction/diagnostic files.  Those
files classify explicit witness-list order failure and overlap; importing Beam
entry/exit vocabulary into them would blur the current module split.  The
lightweight consumer layer therefore stays here, above the diagnostic modules:
it projects the cp223 package into the exact facts a diagnostic caller is most
likely to need.

These theorems deliberately consume the packaged shape instead of rebuilding
the left/right facts directly.  This keeps the future call site small while
preserving the local-only contract: one supplied pulse, or one supplied witness
with membership in one supplied list.
-/

/--
Diagnostic-facing projection for one interval pulse.

From the packaged entry/exit edge shape, recover the paired mass-balance
classification: True Beam at the entry edge and False/Boundary at the exit
edge.
-/
theorem sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
        SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) ∧
      SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
        SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) := by
  rcases sourcePressureBeamPulse_edges_of_intervalPulseAddress A with
    ⟨hentry, hexit⟩
  exact
    ⟨sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget hentry,
      sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget hexit⟩

/--
Diagnostic-facing projection for one witness-generated singleton pulse.

The result keeps exactly the two facts that an obstruction consumer can use
without claiming coverage: the selected addressed depth at the singleton
center/right edge, and the False/Boundary mass-balance comparison at that same
exit edge.
-/
theorem sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamAddressedDepthTarget L
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
      SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
        SourcePressureBeamMassBalanceLeftInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
  rcases sourcePressureBeamPulse_witness_singleton_shape hmem with
    ⟨_, hdepth, hexit⟩
  exact
    ⟨hdepth,
      sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget hexit⟩

/--
Caller-facing full diagnostic for one explicitly contained witness singleton.

This is only a convenience package for one witness `W` with `W ∈ L`.  It
combines the existing singleton edge comparisons with the list-relative
addressed-depth fact:

* entry edge: True Beam comparison `left < right`;
* center/right edge: `SourcePressureBeamAddressedDepthTarget L ...`;
* exit edge: False/Boundary comparison `right <= left`.

No list coverage, witness-family aggregation, canonical target selection,
overlap repair, propagation, or convergence is claimed.
-/
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
      SourcePressureBeamAddressedDepthTarget L
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
        SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
          SourcePressureBeamMassBalanceLeftInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
  rcases sourcePressureBeamPulse_witness_singleton_massBalance_edges W with
    ⟨hentry, hexitBalance⟩
  rcases sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance hmem with
    ⟨hdepth, _⟩
  exact ⟨hentry, hdepth, hexitBalance⟩

/--
A Beam seed exposes one witness whose singleton pulse has the full local
entry-depth-exit diagnostic.

This is the cp227-r1 Branch B higher-level consumer of
`sourcePressureBeamPulse_witness_singleton_full_diagnostic`.  The seed layer
already contains an existential witness membership; this theorem only keeps
that witness explicit and applies the full diagnostic package to it.

It is intentionally existential and local.  It does not choose a canonical
witness, cover the whole list, aggregate witness families, repair overlaps,
propagate the diagnostic, or assert Collatz convergence.
-/
theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureBeamMassBalanceLeftInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
          SourcePressureBeamMassBalanceRightInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
          SourcePressureBeamAddressedDepthTarget L
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
            SourcePressureBeamMassBalanceRightInt n k r
              ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
                (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
              SourcePressureBeamMassBalanceLeftInt n k r
                ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
                  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
    ⟨_, W, hmem, _⟩
  exact
    ⟨W, hmem,
      sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem⟩

/--
Failure resolution also exposes one witness whose singleton pulse has the full
local entry-depth-exit diagnostic.

This is the cp227-r1 Branch C experiment.  It is intentionally placed in the
Beam-facing Pulse layer, not in `PressureAutomaton`: lower diagnostic and
automaton modules must not import Beam vocabulary.

The proof is deliberately thin.  `SourcePressureBeamSeed` is the Beam-facing
name for `SourcePressureFailureResolution`, so this theorem only enters the
seed bridge and reuses the Branch B theorem above.  It does not add a new
failure-resolution decomposition, choose a canonical witness, repair overlap,
or claim list coverage.
-/
theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolution L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureBeamMassBalanceLeftInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
          SourcePressureBeamMassBalanceRightInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
          SourcePressureBeamAddressedDepthTarget L
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
            SourcePressureBeamMassBalanceRightInt n k r
              ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
                (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
              SourcePressureBeamMassBalanceLeftInt n k r
                ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
                  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
  exact exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed h


end DkMath.Collatz
