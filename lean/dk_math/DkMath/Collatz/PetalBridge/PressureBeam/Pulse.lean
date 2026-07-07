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
Centered full diagnostic for one explicitly contained witness singleton.

This is the cp234 native-depth surface over the interval-pulse diagnostic
above.  A witness-generated pulse is a singleton address:

* its entry edge is `W.val - 1`;
* its center/right edge is `W.val`.

The proof only normalizes coordinates using the Core alignment lemmas.  It
does not rebuild low-level edge proofs, transport diagnostics to arbitrary
targets, select a canonical witness, or claim coverage beyond the supplied
membership `W ∈ L`.
-/
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
      SourcePressureBeamAddressedDepthTarget L W.val ∧
        SourcePressureBeamMassBalanceRightInt n k r W.val ≤
          SourcePressureBeamMassBalanceLeftInt n k r W.val := by
  rcases sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem with
    ⟨hentry, hdepth, hexit⟩
  have hstart :=
    sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq W
  have hright :=
    sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq W
  exact
    ⟨by simpa [hstart] using hentry,
      by simpa [hright] using hdepth,
      by simpa [hright] using hexit⟩

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
A Beam seed exposes one witness whose singleton pulse has the centered full
local diagnostic at native depth `W.val`.

This is the cp234 seed bridge.  It combines the existing seed witness
extraction with the centered singleton diagnostic above.  The witness remains
existential: the theorem does not choose a canonical witness, cover the list,
aggregate witnesses, repair overlap, propagate diagnostics, or assert Collatz
convergence.
-/
theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W.val := by
  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
    ⟨_, W, hmem, _⟩
  exact
    ⟨W, hmem,
      sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center hmem⟩

/--
A Beam seed exposes one witness whose centered diagnostic also gives the local
margin-sign transition around the native depth `W.val`.

The index convention is the Beam edge convention:

* mass-balance at edge `j` classifies the next margin `r + j + 1`;
* therefore the entry comparison at `W.val - 1` gives positivity at `r + W.val`;
* the exit comparison at `W.val` gives nonpositivity at `r + W.val + 1`.

The previous margin nonpositivity at `W.val - 1` is read from the local-island
witness itself.  This theorem remains witness-local and seed-existential: it
does not choose a canonical witness, aggregate a family, repair overlaps,
propagate the transition, or claim Collatz convergence.
-/
theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
  rcases exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
      hseed with
    ⟨W, hmem, hentry, haddr, hexit⟩
  have hlocal :=
    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
  rcases hlocal with ⟨hWpos, _hcenterLocal, hprev, _hnextLocal⟩
  have hcenterFromEntry :
      0 < SourcePressureMarginInt n k (r + W.val) := by
    have hentryNext :
        0 < SourcePressureMarginInt n k (r + (W.val - 1) + 1) :=
      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
        n k r (W.val - 1)).2 hentry
    have hidx : r + (W.val - 1) + 1 = r + W.val := by
      omega
    simpa [hidx] using hentryNext
  have hnextFromExit :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr hexit
  exact
    ⟨W, hmem, hprev, hcenterFromEntry, haddr, hnextFromExit⟩

/--
Centered local pulse box for one Beam witness.

This predicate is the cp238 local packaging of three already-established
layers:

* cp235 sign transition around the native witness depth `W.val`;
* cp236 margin-height boxes at the previous, center, and next depths;
* cp237 net-drop jump boxes at the entry and exit adjacent edges.

The predicate is intentionally local and witness-relative.  It does not assert
propagation, list-wide coverage, witness aggregation, overlap repair, canonical
witness selection, monotone trend, global Big bounds, or Collatz convergence.
-/
def SourcePressureBeamCenteredLocalPulseBox
    (n : OddNat) (k r : ℕ)
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W : SourcePressureLocalIslandWitness n k r) : Prop :=
  W ∈ L ∧
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureBeamAddressedDepthTarget L W.val ∧
          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
            (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + (W.val - 1)) ∧
              SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 2 * (k : ℤ)) ∧
              (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + W.val) ∧
                SourcePressureMarginInt n k (r + W.val) ≤ 2 * (k : ℤ)) ∧
                (- (k : ℤ) ≤ SourcePressureMarginInt n k (r + W.val + 1) ∧
                  SourcePressureMarginInt n k (r + W.val + 1) ≤ 2 * (k : ℤ)) ∧
                  (- (3 * (k : ℤ)) ≤
                      SourcePressureNetDropInt n k r (W.val - 1) ∧
                    SourcePressureNetDropInt n k r (W.val - 1) ≤
                      3 * (k : ℤ)) ∧
                    (- (3 * (k : ℤ)) ≤
                        SourcePressureNetDropInt n k r W.val ∧
                      SourcePressureNetDropInt n k r W.val ≤
                        3 * (k : ℤ))

/--
Project the sign-and-target part of a centered local pulse box.

This is the cp239 Branch C consumer surface.  It exposes the part that a future
neighbor/transport theorem will usually need first, while leaving the finite
height and jump boxes inside `SourcePressureBeamCenteredLocalPulseBox` for
callers that need quantitative bounds.

No neighboring witness, transport, propagation, or obstruction is inferred
from this projection.
-/
theorem SourcePressureBeamCenteredLocalPulseBox.signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W) :
    W ∈ L ∧
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
  rcases hbox with
    ⟨hmem, hprev, hcenter, haddr, hnext, _hprevBox, _hcenterBox,
      _hnextBox, _hentryJumpBox, _hexitJumpBox⟩
  exact ⟨hmem, hprev, hcenter, haddr, hnext⟩

/--
Beam-facing neighbor-candidate surface for explicit adjacent witnesses.

This is only a symmetric naming wrapper around the existing list/pair address
predicate.  It deliberately does not say that a boxed pulse produces a
neighbor.  The neighbor candidate must come from explicit list adjacency:

* either `W` is immediately before `W'` in `L`;
* or `W'` is immediately before `W` in `L`.

No propagation, transport, coverage, sorting, or overlap repair is asserted.
-/
def SourcePressureBeamNeighborCandidate
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
    SourcePressureLocalIslandWitnessAdjacentPairInList L W' W

/--
Consume a boxed local pulse together with an explicit neighbor candidate.

The theorem only packages the supplied adjacency candidate with the sign and
target facts projected from the box.  It does not assert that `W'` has a pulse
box, that transport succeeds, or that a neighbor exists from the box alone.
-/
theorem SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W)
    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
    SourcePressureBeamNeighborCandidate L W W' ∧
      W ∈ L ∧
        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
  ⟨hneigh, hbox.signs⟩

/--
The left endpoint of an explicit Beam neighbor candidate is in the witness
list.

This is only an adjacency projection.  It does not infer a neighbor from a
local pulse box, does not assert that either endpoint has a pulse box, and does
not transport any diagnostic information.
-/
theorem sourcePressureBeamNeighborCandidate_left_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
    W ∈ L := by
  rcases hneigh with hleft | hright
  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hleft
  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hright

/--
The right endpoint of an explicit Beam neighbor candidate is in the witness
list.

The witness `W'` is available because it is one endpoint of the supplied
symmetric adjacent-pair evidence.  This is not derived from
`SourcePressureBeamCenteredLocalPulseBox`, and it does not claim propagation or
transport from `W` to `W'`.
-/
theorem sourcePressureBeamNeighborCandidate_right_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
    W' ∈ L := by
  rcases hneigh with hleft | hright
  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hleft
  · exact sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hright

/--
An explicit Beam neighbor candidate exposes the neighboring witness's centered
singleton diagnostic.

This theorem is the safe cp241 neighbor bridge:

* adjacency gives `W' ∈ L`;
* membership lets the existing singleton theorem read the centered diagnostic
  at `W'.val`.

It deliberately does not say that `W'` has a centered local pulse box, that a
box for `W` creates the neighbor, or that any transport/propagation succeeds.
-/
theorem sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hneigh : SourcePressureBeamNeighborCandidate L W W') :
    SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
      SourcePressureBeamAddressedDepthTarget L W'.val ∧
        SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
          SourcePressureBeamMassBalanceLeftInt n k r W'.val :=
  sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
    (sourcePressureBeamNeighborCandidate_right_mem hneigh)

/--
A Beam seed exposes one witness whose centered pulse is inside the finite
local pulse box.

This is only a thin wrapper over:

* `exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed`;
* `sourcePressureMarginInt_bounds_window`;
* `sourcePressureNetDropInt_bounds_window`.

It packages the local sign transition, three pointwise height boxes, and two
adjacent jump boxes for the same existential witness.  No propagation or
global behavior is claimed.
-/
theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      SourcePressureBeamCenteredLocalPulseBox n k r L W := by
  rcases exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
      hseed with
    ⟨W, hmem, hprev, hcenter, haddr, hnext⟩
  exact
    ⟨W,
      hmem,
      hprev,
      hcenter,
      haddr,
      hnext,
      sourcePressureMarginInt_bounds_window n k (r + (W.val - 1)),
      sourcePressureMarginInt_bounds_window n k (r + W.val),
      sourcePressureMarginInt_bounds_window n k (r + W.val + 1),
      sourcePressureNetDropInt_bounds_window n k r (W.val - 1),
      sourcePressureNetDropInt_bounds_window n k r W.val⟩

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

/--
An addressed adjacent pair preserves the left witness identity for the full
local singleton diagnostic.

This is the cp228 Branch A left-side bridge.  The recovered branch of
`SourcePressureFailureResolution` exposes an adjacent pair `A B` through
`SourcePressureLocalIslandWitnessAdjacentPairInList L A B`; this theorem keeps
the left witness `A` rather than collapsing immediately to an arbitrary
existential witness.

The proof only extracts `A ∈ L` from the adjacent-pair address and then applies
`sourcePressureBeamPulse_witness_singleton_full_diagnostic`.  It does not
select a canonical pair, aggregate over pairs, or claim coverage.
-/
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
    SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) ∧
      SourcePressureBeamAddressedDepthTarget L
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ∧
        SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ≤
          SourcePressureBeamMassBalanceLeftInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) := by
  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic
    (sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin)

/--
An addressed adjacent pair preserves the right witness identity for the full
local singleton diagnostic.

This is the cp228 Branch A right-side bridge.  It is symmetric in spirit to
the left-side bridge, but it is kept as a separate theorem because downstream
recovered-pair callers may care whether the diagnostic came from `A` or `B`.

The theorem only extracts `B ∈ L` from the adjacent-pair address and applies
the existing singleton full diagnostic.  It does not prefer this side globally
or assert that both sides cover a larger interval.
-/
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
    SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start - 1) ∧
      SourcePressureBeamAddressedDepthTarget L
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) ∧
        SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) ≤
          SourcePressureBeamMassBalanceLeftInt n k r
            ((sourcePressureIntervalPulseAddress_of_localIslandWitness B).start +
              (sourcePressureIntervalPulseAddress_of_localIslandWitness B).len - 1) := by
  exact sourcePressureBeamPulse_witness_singleton_full_diagnostic
    (sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin)

/--
An adjacent-overlap obstruction exposes a branch-specific left witness with
the full singleton pulse diagnostic.

This is the Beam-facing cp230 wrapper over
`exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction`.  The
lower theorem supplies the addressed adjacent pair and the pair-local overlap
obstruction; this wrapper only applies the existing left-side singleton
diagnostic for that addressed pair.

The conclusion keeps the addressed pair and the overlap obstruction visible.
It does not repair the overlap, choose a canonical obstructing pair, aggregate
several pairs, transport the diagnostic to arbitrary targets, or claim
coverage of the witness list.
-/
theorem
    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B ∧
          SourcePressureBeamMassBalanceLeftInt n k r
              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) <
            SourcePressureBeamMassBalanceRightInt n k r
              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start - 1) ∧
            SourcePressureBeamAddressedDepthTarget L
              ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
                (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ∧
              SourcePressureBeamMassBalanceRightInt n k r
                ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
                  (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) ≤
                SourcePressureBeamMassBalanceLeftInt n k r
                  ((sourcePressureIntervalPulseAddress_of_localIslandWitness A).start +
                    (sourcePressureIntervalPulseAddress_of_localIslandWitness A).len - 1) := by
  rcases exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction hobs with
    ⟨A, B, hin, hobspair⟩
  exact
    ⟨A, B, hin, hobspair,
      sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
        hin⟩

/--
An adjacent-overlap obstruction exposes some listed witness with the full
singleton pulse diagnostic.

This is the intentionally weaker caller surface for users that only need an
existential pulse diagnostic and do not care which endpoint of the obstructing
adjacent pair produced it.  It consumes the cp230 left-witness wrapper, so it
does not re-run the overlap recursion and does not introduce a canonical
selection principle: the witness is merely the left endpoint supplied by one
addressed overlap pair.

The stronger pair-preserving theorem remains
`exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction`.
Use this weaker theorem only when preserving `A`, `B`, and the pair-overlap
obstruction would be caller noise.
-/
theorem exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
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
  rcases
    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
      hobs with
    ⟨A, B, hin, _hobspair, hdiag⟩
  exact
    ⟨A, sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin,
      hdiag⟩


end DkMath.Collatz
