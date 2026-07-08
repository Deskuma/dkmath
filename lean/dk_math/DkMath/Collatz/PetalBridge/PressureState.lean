/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureBeam

#print "file: DkMath.Collatz.PetalBridge.PressureState"

namespace DkMath.Collatz

/-
Mnemonic state layer for the source-pressure proof automaton.

This file is intentionally a thin naming layer over the already proved
pressure/Beam predicates.  The goal is not to create an executable automaton
yet.  The current goal is a readable state table:

```text
SortedFailure
  -> FailureResolution
  -> BeamSeed
  -> CenteredPulseBox
  -> NeighborCandidate
  -> OrientedNeighborDiagnostic
```

Each state below is still a `Prop`: it means that the proof currently has
evidence for that named local configuration.  Transitions are theorem arrows
between those named states.  This keeps the automaton Lean-native: movement is
movement of evidence, not computation over an unproved global process.

Important guardrail for future work:

* these names do not assert total coverage of all possible lists;
* they do not choose canonical witnesses or canonical adjacent pairs;
* they do not repair overlap;
* they do not propagate local diagnostics;
* they do not prove Collatz convergence.

The eventual "mnemonic table" can refine these names into bit patterns.  For
now, the bits are deliberately informal and local:

* `F`: sorted-before failure is present;
* `R`: failure has resolved into recovered-pair or overlap evidence;
* `S`: Beam seed state is available;
* `P`: a centered local pulse box is available for a supplied witness;
* `N`: an explicit neighbor candidate is available;
* `D`: an oriented adjacent diagnosis is available.
-/

/-- Mnemonic names for the current proof-automaton nodes. -/
inductive SourcePressureStateName where
  | sortedFailure
  | failureResolution
  | recoveredAdjacent
  | adjacentOverlap
  | beamSeed
  | centeredPulseBox
  | neighborCandidate
  | orientedNeighborDiagnostic
  deriving DecidableEq, Repr

/--
Mnemonic names for currently unfilled or unconfirmed regions of the
source-pressure proof automaton.

These are intentionally names only.  They are the future opcode slots for
places where the proof-flow can get stuck because one required piece of
evidence has not yet been supplied or derived.

The key distinction is:

* a Gap name is not a contradiction;
* a Gap name is not a theorem saying that evidence is impossible;
* a Gap name is a stable label for "this transition has no assigned proof
  opcode yet".

Future work can attach proof-producing opcodes, impossibility theorems, or
obstruction witnesses to these names one by one.
-/
inductive SourcePressureGapName where
  /-- No sorted-before failure input has been supplied yet. -/
  | missingFailureInput
  /-- Failure resolution has not yet been split into recovered/overlap. -/
  | unresolvedResolutionBranch
  /-- A Beam seed is not yet available from the current evidence. -/
  | missingBeamSeed
  /-- A centered pulse box has not yet been produced for the selected witness. -/
  | missingPulseBox
  /-- A neighbor candidate has not yet been supplied by explicit adjacency. -/
  | missingNeighborCandidate
  /-- A symmetric neighbor candidate is known, but no ordered orientation is fixed. -/
  | missingOrientation
  /-- Orientation is known, but adjacent diagnosis evidence is not yet attached. -/
  | missingAdjacentDiagnosis
  /-- Overlap has appeared and remains an unresolved obstruction. -/
  | unresolvedOverlapObstruction
  /-- A local diagnostic exists, but no transport/propagation theorem applies. -/
  | missingTransport
  /-- A local witness is known, but no canonical selection principle is available. -/
  | missingCanonicalSelection
  /-- Local evidence exists, but list-wide coverage has not been proved. -/
  | missingCoverage
  /-- Local families exist, but no safe aggregation theorem has been assigned. -/
  | missingAggregation
  deriving DecidableEq, Repr

/--
Mnemonic opcode names for proof steps that may later fill Gap slots.

At this stage these are labels, not executable code.  They name the kinds of
proof-producing moves already visible in the project:

* enter a state from existing evidence;
* split a branch;
* project endpoint facts;
* attach an orientation;
* attach a lower adjacent diagnosis;
* close a branch as obstruction.

Keeping these names separate from `SourcePressureGapName` makes the intended
table shape explicit:

```text
state bits + gap name -- assigned opcode --> next named state
```
-/
inductive SourcePressureOpcodeName where
  | enterFailureResolution
  | splitResolution
  | enterBeamSeed
  | extractPulseBox
  | projectNeighborMembership
  | projectNeighborDiagnostic
  | attachForwardOrientation
  | attachReverseOrientation
  | attachAdjacentDiagnosis
  | closeAsOverlapObstruction
  | markNoTransport
  | markNoCoverage
  | markNoCanonicalSelection
  deriving DecidableEq, Repr

/-
Gap/opcode table notes.

Current named states already cover the positive path up to oriented local
diagnostics.  The first important unfilled cells are:

```text
NeighborCandidate alone
  -> missingOrientation
  -> missingAdjacentDiagnosis

CenteredPulseBox alone
  -> missingBeamSeed

OrientedNeighborDiagnostic
  -> missingTransport
  -> missingCoverage
```

These are not Lean theorems yet.  They are the mnemonic slots that future
formal impossibility lemmas or additional bridge theorems can target.
-/

/--
State bit `F`: sorted-before failure has been observed for the supplied
witness list.
-/
def SourcePressureSortedFailureState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L

/--
State bit `R`: the local failure-resolution automaton has split the failure
into recovered-adjacent evidence or adjacent-overlap obstruction.
-/
def SourcePressureFailureResolutionState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureFailureResolution L

/--
Recovered branch of the resolution state: some addressed adjacent pair carries
the named pair-local recovered diagnostic.
-/
def SourcePressureRecoveredAdjacentState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
        A B

/--
Overlap branch of the resolution state: adjacent overlap is present as an
obstruction on the supplied witness list.
-/
def SourcePressureAdjacentOverlapState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

/--
State bit `S`: Beam-facing seed state.  This is the Beam name for failure
resolution.
-/
def SourcePressureBeamSeedState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureBeamSeed L

/--
State bit `P`: a centered local pulse box is available for one supplied
witness.
-/
def SourcePressureCenteredPulseBoxState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureBeamCenteredLocalPulseBox n k r L W

/--
State bit `N`: an explicit symmetric neighbor candidate is available for two
supplied witnesses.
-/
def SourcePressureNeighborCandidateState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureBeamNeighborCandidate L W W'

/--
State bit `D`: an oriented adjacent diagnosis is available and the two
endpoints expose their centered Beam diagnostics.

The orientation is part of the state.  The first component is the ordered
adjacent-pair address; the second component is the lower adjacent diagnosis;
the remaining components are Beam-centered endpoint diagnostics.
-/
def SourcePressureOrientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' ∧
      SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
        SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
        SourcePressureBeamAddressedDepthTarget L W.val ∧
          SourcePressureBeamMassBalanceRightInt n k r W.val ≤
            SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
            SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
              SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
              SourcePressureBeamAddressedDepthTarget L W'.val ∧
                SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
                  SourcePressureBeamMassBalanceLeftInt n k r W'.val

/-- Generic proof-automaton transition: evidence for `S` can be moved to `T`. -/
def SourcePressureStateTransition (S T : Prop) : Prop :=
  S → T

/-- `F -> R`: sorted-before failure enters the failure-resolution state. -/
theorem sourcePressureSortedFailureState_to_failureResolutionState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureSortedFailureState L) :
    SourcePressureFailureResolutionState L :=
  sourcePressureFailureResolution_of_sortedBeforeFailure h

/-- `R -> S`: failure resolution is exactly the Beam seed handoff state. -/
theorem sourcePressureFailureResolutionState_to_beamSeedState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    SourcePressureBeamSeedState L :=
  h

/-- `S -> R`: the Beam seed state can be read back as failure resolution. -/
theorem sourcePressureBeamSeedState_to_failureResolutionState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamSeedState L) :
    SourcePressureFailureResolutionState L :=
  h

/-- `F -> S`: sorted-before failure reaches the Beam seed handoff state. -/
theorem sourcePressureSortedFailureState_to_beamSeedState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureSortedFailureState L) :
    SourcePressureBeamSeedState L :=
  sourcePressureBeamSeed_of_sortedBeforeFailure h

/-- Recovered adjacent evidence is the recovered branch of resolution. -/
theorem sourcePressureRecoveredAdjacentState_to_failureResolutionState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    SourcePressureFailureResolutionState L :=
  Or.inl h

/-- Adjacent overlap evidence is the overlap branch of resolution. -/
theorem sourcePressureAdjacentOverlapState_to_failureResolutionState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureAdjacentOverlapState L) :
    SourcePressureFailureResolutionState L :=
  Or.inr h

/-- Split the failure-resolution state into its two mnemonic branches. -/
theorem sourcePressureFailureResolutionState_cases
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    SourcePressureRecoveredAdjacentState L ∨
      SourcePressureAdjacentOverlapState L :=
  h

/-
`P -> S`: a centered local pulse box remembers the witness membership part of
the Beam seed surface only through its enclosing list state.

This theorem is intentionally not provided yet.  A pulse box alone does not
construct `SourcePressureBeamSeedState L`; the seed is an upstream state.
Keeping this absence explicit prevents a common false transition in the future
mnemonic table.
-/

/-- `P -> N + signs`: reuse the existing boxed-pulse and neighbor projection. -/
theorem sourcePressureCenteredPulseBoxState_signs_of_neighborCandidateState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureCenteredPulseBoxState L W)
    (hneigh : SourcePressureNeighborCandidateState L W W') :
    SourcePressureBeamNeighborCandidate L W W' ∧
      W ∈ L ∧
        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
  SourcePressureBeamCenteredLocalPulseBox.signs_of_neighborCandidate
    hbox hneigh

/--
`N -> centered diagnostic for W'`: neighbor-candidate state exposes the
neighbor endpoint diagnostic.
-/
theorem sourcePressureNeighborCandidateState_right_center_full_diagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hneigh : SourcePressureNeighborCandidateState L W W') :
    SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
      SourcePressureBeamAddressedDepthTarget L W'.val ∧
        SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
          SourcePressureBeamMassBalanceLeftInt n k r W'.val :=
  sourcePressureBeamNeighborCandidate_right_center_full_diagnostic hneigh

/--
Forward oriented adjacent diagnosis enters mnemonic state `D`.

The underlying Beam theorem also returns the symmetric neighbor candidate.
This mnemonic state keeps only the ordered diagnostic orientation and the two
endpoint centered diagnostics.
-/
theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W') :
    SourcePressureOrientedNeighborDiagnosticState L W W' := by
  rcases
    sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
      hin hdiag with
    ⟨_hneigh, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩
  exact
    ⟨hin, hdiag', hWentry, hWaddr, hWexit, hW'entry, hW'addr, hW'exit⟩

/--
Project the left endpoint margin-sign pattern from an oriented neighbor
diagnostic state.

The oriented state stores mass-balance entry/exit comparisons for `W`.
Together with the local-island witness property, these comparisons recover the
three-margin pattern around the native depth `W.val`:

```text
r + (W.val - 1) <= 0
r + W.val       >  0
r + W.val + 1   <= 0
```

This is a pure projection from state `D`; it does not add transport,
propagation, coverage, or canonical witness selection.
-/
theorem sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureBeamAddressedDepthTarget L W.val ∧
          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
  rcases h with
    ⟨_hin, _hdiag, hentry, haddr, hexit, _hentry', _haddr', _hexit'⟩
  have hlocal :=
    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
  rcases hlocal with ⟨_hWpos, _hcenterLocal, hprev, _hnextLocal⟩
  have hcenter :
      0 < SourcePressureMarginInt n k (r + W.val) := by
    have hentryNext :
        0 < SourcePressureMarginInt n k (r + (W.val - 1) + 1) :=
      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
        n k r (W.val - 1)).2 hentry
    have hidx : r + (W.val - 1) + 1 = r + W.val := by
      omega
    simpa [hidx] using hentryNext
  have hnext :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr hexit
  exact ⟨hprev, hcenter, haddr, hnext⟩

/--
Project the right endpoint margin-sign pattern from an oriented neighbor
diagnostic state.

This is the same projection as the left endpoint theorem, but applied to the
oriented neighbor endpoint `W'`.  The proof deliberately reads only the local
fields already stored in state `D`.
-/
theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
    SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W'.val) ∧
        SourcePressureBeamAddressedDepthTarget L W'.val ∧
          SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 := by
  rcases h with
    ⟨_hin, _hdiag, _hentry, _haddr, _hexit, hentry', haddr', hexit'⟩
  have hlocal :=
    (sourcePressureLocalIsland_iff_margin n k r W'.val).1 W'.property
  rcases hlocal with ⟨_hW'pos, _hcenterLocal, hprev, _hnextLocal⟩
  have hcenter :
      0 < SourcePressureMarginInt n k (r + W'.val) := by
    have hentryNext :
        0 < SourcePressureMarginInt n k (r + (W'.val - 1) + 1) :=
      (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
        n k r (W'.val - 1)).2 hentry'
    have hidx : r + (W'.val - 1) + 1 = r + W'.val := by
      omega
    simpa [hidx] using hentryNext
  have hnext :
      SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 :=
    sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr' hexit'
  exact ⟨hprev, hcenter, haddr', hnext⟩

/--
Two-endpoint box state for an oriented neighbor diagnostic.

This packages state `D` together with the finite local pulse box at both
endpoints.  Each endpoint box contains:

* the three-margin sign pattern around the native depth;
* margin-height bounds at previous, center, and next depths;
* net-drop bounds at the entry and exit adjacent edges.

Using the existing `SourcePressureBeamCenteredLocalPulseBox` keeps the
one-endpoint box contract authoritative and prevents this two-endpoint state
from silently drifting if the pulse-box API is refined later.

This is still a local two-endpoint package.  It does not assert transport,
propagation, coverage, aggregation, overlap repair, or convergence.
-/
def SourcePressureOrientedNeighborBoxState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureOrientedNeighborDiagnosticState L W W' ∧
    SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
      SourcePressureBeamCenteredLocalPulseBox n k r L W'

/-- Project the oriented diagnostic component from a two-endpoint box state. -/
theorem SourcePressureOrientedNeighborBoxState.diagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureOrientedNeighborDiagnosticState L W W' := by
  rcases h with ⟨hD, _hL, _hR⟩
  exact hD

/-- Project the left endpoint centered local pulse box from a two-endpoint box state. -/
theorem SourcePressureOrientedNeighborBoxState.left_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W := by
  rcases h with ⟨_hD, hL, _hR⟩
  exact hL

/-- Project the right endpoint centered local pulse box from a two-endpoint box state. -/
theorem SourcePressureOrientedNeighborBoxState.right_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W' := by
  rcases h with ⟨_hD, _hL, hR⟩
  exact hR

/--
Project the ordered adjacent-pair address from an oriented diagnostic state.

This is the orientation hook needed by the next comparison layer:

```text
Box -> D -> AdjacentPairInList L W W'
```
-/
theorem SourcePressureOrientedNeighborDiagnosticState.adjacentPair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' := by
  rcases h with ⟨hin, _hdiag, _hentry, _haddr, _hexit, _hentry', _haddr', _hexit'⟩
  exact hin

/-- Project the ordered adjacent-pair address from a two-endpoint box state. -/
theorem SourcePressureOrientedNeighborBoxState.adjacentPair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
  h.diagnostic.adjacentPair

/-
Order-projection note for the next comparison layer.

`SourcePressureLocalIslandWitnessAdjacentPairInList L W W'` is the strongest
order relation currently stored in `SourcePressureOrientedNeighborBoxState`.
It says that `W` and `W'` occur as an ordered neighboring pair in the explicit
list `L`.

It does *not* contain either of the following stronger facts:

```text
SourcePressureLocalIslandWitnessBefore W W'
W.val < W'.val
```

Those facts concern interval-pulse address order / numeric depth order.  They
are not derivable from list adjacency alone without an additional invariant
saying that the witness list is sorted by address/depth.  The comparison layer
should therefore consume the ordered adjacent-pair address first, then add the
required sortedness/address-order hypothesis explicitly.
-/

/--
Project the strongest currently available ordered pair relation from a
two-endpoint box: `W` and `W'` are adjacent in this order in the enclosing list.

This is intentionally an alias of `.adjacentPair` with a more comparison-facing
name.  It is not a witness-level `Before` theorem and not a numeric value-order
theorem.
-/
theorem SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
  h.adjacentPair

/-- The left endpoint of a two-endpoint box is a member of the enclosing list. -/
theorem SourcePressureOrientedNeighborBoxState.left_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    W ∈ L :=
  sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
    h.orderedAdjacentPairInList

/-- The right endpoint of a two-endpoint box is a member of the enclosing list. -/
theorem SourcePressureOrientedNeighborBoxState.right_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    W' ∈ L :=
  sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
    h.orderedAdjacentPairInList

/--
An addressed adjacent pair in a sorted witness list inherits witness-level
`Before`.

This is the missing comparison bridge found at cp256.  The sortedness
predicate already exists as `SourcePressureLocalIslandWitnessListSortedBefore`;
it is adjacent sortedness after converting witnesses to interval-pulse
addresses.  Since `SourcePressureLocalIslandWitnessAdjacentPairInList` has the
same head-or-tail recursive shape, the bridge is a structural induction over
the enclosing list.

This theorem does not prove any numeric value order such as `W.val < W'.val`.
It only turns list adjacency plus address-sortedness into witness-level
ordered non-overlap.
-/
theorem sourcePressureAdjacentPairInList_before_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    SourcePressureLocalIslandWitnessBefore W W' := by
  induction L generalizing W W' with
  | nil =>
      exact False.elim hin
  | cons A rest ih =>
      cases rest with
      | nil =>
          exact False.elim hin
      | cons B rest =>
          rcases hin with hhead | htail
          · rcases hhead with ⟨hW, hW'⟩
            subst W
            subst W'
            change
              SourcePressureIntervalPulseAddressBefore
                (sourcePressureIntervalPulseAddress_of_localIslandWitness A)
                (sourcePressureIntervalPulseAddress_of_localIslandWitness B)
            change
              SourcePressureIntervalPulseAddressFamilySortedBefore
                (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
                  (A :: B :: rest)) at hsorted
            exact hsorted.1
          · have htailSorted :
                SourcePressureLocalIslandWitnessListSortedBefore (B :: rest) := by
              change
                SourcePressureIntervalPulseAddressFamilySortedBefore
                  (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
                    (A :: B :: rest)) at hsorted
              change
                SourcePressureIntervalPulseAddressFamilySortedBefore
                  (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
                    (B :: rest))
              exact hsorted.2
            exact ih htailSorted htail

/--
Box-facing version of
`sourcePressureAdjacentPairInList_before_of_sorted`.

A two-endpoint box supplies the ordered adjacent-pair address; sortedness of
the enclosing witness list supplies the mathematical address order.
-/
theorem SourcePressureOrientedNeighborBoxState.before_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    SourcePressureLocalIslandWitnessBefore W W' :=
  sourcePressureAdjacentPairInList_before_of_sorted hsorted
    hbox.orderedAdjacentPairInList

/--
Address-level projection of `before_of_sorted`.

`SourcePressureLocalIslandWitnessBefore` is definitionally the address-level
`SourcePressureIntervalPulseAddressBefore` relation after converting both
witnesses to singleton interval-pulse addresses.  This theorem keeps that
definition available under a box-facing name so later comparison proofs can
work directly with address coordinates.
-/
theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    SourcePressureIntervalPulseAddressBefore
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W') :=
  hbox.before_of_sorted hsorted

/--
Address-coordinate form of the ordered box comparison.

The address-level before relation is `A.start + A.len ≤ B.start`.  Since
interval-pulse addresses have positive length, this gives a strict separation
between the left endpoint's right edge `A.start + A.len - 1` and the right
endpoint's start.

This is still only an address comparison.  It does not claim coverage,
transport, or global monotonicity of all pressure depths.
-/
theorem SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 <
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W').start := by
  have hbefore := hbox.addressBefore_of_sorted hsorted
  have hlen :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len :=
    SourcePressureIntervalPulseAddress.len_pos
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
  unfold SourcePressureIntervalPulseAddressBefore at hbefore
  omega

/--
Non-strict version of `rightEdge_lt_start_of_sorted`.

This wrapper is useful for callers that consume non-overlap as a weak
inequality while the strict version remains available for depth comparison.
-/
theorem SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 ≤
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W').start :=
  le_of_lt (hbox.rightEdge_lt_start_of_sorted hsorted)

/--
Value-level comparison extracted from a sorted oriented neighbor box.

For local-island witnesses, the generated interval-pulse address is a
singleton: its start and right edge are both `W.val`.  Therefore the
address-level strict separation becomes the native depth comparison
`W.val < W'.val`.

This theorem is the strongest direct numeric comparison available from the
current definitions: it depends on the explicit adjacent pair inside the box
and on the sortedness invariant for the enclosing witness list.
-/
theorem SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    W.val < W'.val := by
  have hsep := hbox.rightEdge_lt_start_of_sorted hsorted
  rw [sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq,
    sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq] at hsep
  exact hsep

/-- Non-strict value-level wrapper for callers that only need `≤`. -/
theorem SourcePressureOrientedNeighborBoxState.val_le_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    W.val ≤ W'.val :=
  le_of_lt (hbox.val_lt_of_sorted hsorted)

/--
Sorted oriented neighbor boxes have distinct endpoint depths.

This is a caller-facing corollary of `val_lt_of_sorted`, useful when later
non-collision arguments need only inequality rather than the full order.
-/
theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    W.val ≠ W'.val :=
  ne_of_lt (hbox.val_lt_of_sorted hsorted)

/--
Sorted oriented neighbor boxes rule out the reverse value order.

This is the negative-orientation wrapper for callers that want to discharge a
reverse comparison branch directly from the sorted box state.
-/
theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    ¬ W'.val ≤ W.val :=
  not_le_of_gt (hbox.val_lt_of_sorted hsorted)

/--
A sorted witness list forbids the same box from appearing in the reverse
orientation.

The forward box gives `W.val < W'.val`; a reverse box over the same sorted list
would give `W'.val ≤ W.val`.  The two facts are incompatible.  This is a local
orientation exclusion only: it does not select a canonical box globally and does
not assert coverage of all possible neighbor pairs.
-/
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    ¬ SourcePressureOrientedNeighborBoxState L W' W := by
  intro hrev
  exact hbox.not_val_ge_of_sorted hsorted
    (hrev.val_le_of_sorted hsorted)

/--
Named state for the forward comparison branch of a two-endpoint box.

This packages the exact payload produced under sortedness:

* the oriented neighbor box itself;
* the forward native depth comparison `W.val < W'.val`;
* exclusion of the reverse box orientation.

It is a local pair-comparison state, not a canonical-pair selector and not a
global coverage statement.
-/
def SourcePressureForwardBoxComparisonState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureOrientedNeighborBoxState L W W' ∧
    W.val < W'.val ∧
      ¬ SourcePressureOrientedNeighborBoxState L W' W

/-- Project the underlying oriented neighbor box from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    SourcePressureOrientedNeighborBoxState L W W' :=
  h.1

/-- Project the forward value comparison from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.val_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    W.val < W'.val :=
  h.2.1

/-- Project reverse-box exclusion from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.not_reverse_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    ¬ SourcePressureOrientedNeighborBoxState L W' W :=
  h.2.2

/-- Project the left centered pulse box from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.left_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W :=
  h.box.left_box

/-- Project the right centered pulse box from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.right_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
  h.box.right_box

/-- Project the ordered adjacent-pair address from a forward comparison state. -/
theorem SourcePressureForwardBoxComparisonState.adjacentPair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
  h.box.adjacentPair

/-- The left endpoint of a forward comparison state is a member of the list. -/
theorem SourcePressureForwardBoxComparisonState.left_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    W ∈ L :=
  h.box.left_mem

/-- The right endpoint of a forward comparison state is a member of the list. -/
theorem SourcePressureForwardBoxComparisonState.right_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    W' ∈ L :=
  h.box.right_mem

/--
Pair-comparison-facing packaging of the forward box branch.

This state keeps the forward comparison state and repeats the local pair data
that the next layer naturally consumes:

* the ordered adjacent-pair address;
* the left endpoint's centered pulse box;
* the right endpoint's centered pulse box.

The duplicated projections are intentional.  They keep later pair-comparison
theorems from depending on the internal shape of
`SourcePressureForwardBoxComparisonState`.
-/
def SourcePressureForwardPairComparisonState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureForwardBoxComparisonState L W W' ∧
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
      SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
        SourcePressureBeamCenteredLocalPulseBox n k r L W'

/-- Project the underlying forward box comparison state. -/
theorem SourcePressureForwardPairComparisonState.forward
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureForwardBoxComparisonState L W W' :=
  h.1

/-- Project the ordered adjacent-pair address from a forward pair comparison state. -/
theorem SourcePressureForwardPairComparisonState.adjacentPair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
  h.2.1

/-- Project the left endpoint pulse box from a forward pair comparison state. -/
theorem SourcePressureForwardPairComparisonState.left_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W :=
  h.2.2.1

/-- Project the right endpoint pulse box from a forward pair comparison state. -/
theorem SourcePressureForwardPairComparisonState.right_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
  h.2.2.2

/-- Project the forward value comparison from a forward pair comparison state. -/
theorem SourcePressureForwardPairComparisonState.val_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W.val < W'.val :=
  h.forward.val_lt

/-- Project reverse-box exclusion from a forward pair comparison state. -/
theorem SourcePressureForwardPairComparisonState.not_reverse_box
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    ¬ SourcePressureOrientedNeighborBoxState L W' W :=
  h.forward.not_reverse_box

/-- The left endpoint of a forward pair comparison state is a member of the list. -/
theorem SourcePressureForwardPairComparisonState.left_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W ∈ L :=
  h.left_box.signs.1

/-- The right endpoint of a forward pair comparison state is a member of the list. -/
theorem SourcePressureForwardPairComparisonState.right_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W' ∈ L :=
  h.right_box.signs.1

/--
Project the sign-and-target surface for the left endpoint of a forward pair
comparison state.
-/
theorem SourcePressureForwardPairComparisonState.left_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W ∈ L ∧
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
  h.left_box.signs

/--
Project the sign-and-target surface for the right endpoint of a forward pair
comparison state.
-/
theorem SourcePressureForwardPairComparisonState.right_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W' ∈ L ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
            SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 :=
  h.right_box.signs

/--
Both endpoint centers of a forward pair comparison state are positive, and the
left endpoint is strictly before the right endpoint in value order.
-/
theorem SourcePressureForwardPairComparisonState.center_pos_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      0 < SourcePressureMarginInt n k (r + W'.val) ∧
        W.val < W'.val := by
  rcases h.left_signs with
    ⟨_hmemL, _hprevL, hcenterL, _htargetL, _hnextL⟩
  rcases h.right_signs with
    ⟨_hmemR, _hprevR, hcenterR, _htargetR, _hnextR⟩
  exact ⟨hcenterL, hcenterR, h.val_lt⟩

/--
Both endpoint centers of a forward pair comparison state are addressed beam
targets, and the left endpoint is strictly before the right endpoint in value
order.
-/
theorem SourcePressureForwardPairComparisonState.center_targets_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureBeamAddressedDepthTarget L W.val ∧
      SourcePressureBeamAddressedDepthTarget L W'.val ∧
        W.val < W'.val := by
  rcases h.left_signs with
    ⟨_hmemL, _hprevL, _hcenterL, htargetL, _hnextL⟩
  rcases h.right_signs with
    ⟨_hmemR, _hprevR, _hcenterR, htargetR, _hnextR⟩
  exact ⟨htargetL, htargetR, h.val_lt⟩

/--
Bundle the positive-center and addressed-target pair surfaces into one
caller-facing theorem.

This is the compact comparison surface for the forward pair branch:
two positive centers, two addressed targets, and strict left-to-right value
order.  It remains local to the explicit pair carried by `FPC`.
-/
theorem SourcePressureForwardPairComparisonState.center_pair_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      0 < SourcePressureMarginInt n k (r + W'.val) ∧
        SourcePressureBeamAddressedDepthTarget L W.val ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
            W.val < W'.val := by
  rcases h.center_pos_pair with ⟨hposL, hposR, hlt⟩
  rcases h.center_targets_pair with ⟨htargetL, htargetR, _hlt'⟩
  exact ⟨hposL, hposR, htargetL, htargetR, hlt⟩

/--
Boundary-sign pair surface for the forward pair branch.

Both endpoints are local pulses with nonpositive neighboring margins and a
positive center margin, and the left endpoint is strictly before the right
endpoint in value order.
-/
theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                W.val < W'.val := by
  rcases h.left_signs with ⟨_, hprevL, hcenterL, _, hnextL⟩
  rcases h.right_signs with ⟨_, hprevR, hcenterR, _, hnextR⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, h.val_lt⟩

/--
Lift the forward value order to the actual center indices used by the margin
function.
-/
theorem SourcePressureForwardPairComparisonState.center_index_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val < r + W'.val := by
  have hlt : W.val < W'.val := h.val_lt
  omega

/-- The two center indices of a forward pair comparison state are distinct. -/
theorem SourcePressureForwardPairComparisonState.center_index_ne
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val ≠ r + W'.val :=
  ne_of_lt h.center_index_lt

/--
Boundary-sign pair surface with the order stated at the actual center indices.

This is the same two-pulse boundary surface as
`boundary_sign_pair_surface`, but the final comparison is expressed in the
index language used by `SourcePressureMarginInt`.
-/
theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                r + W.val < r + W'.val := by
  rcases h.boundary_sign_pair_surface with
    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, _hlt⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
    h.center_index_lt⟩

/--
Compact separation surface for the two center indices of a forward pair.

The strict order is the main payload; the non-equality projection is repeated
because many later obstruction and interference lemmas consume `≠` directly.
-/
theorem SourcePressureForwardPairComparisonState.indexed_center_separation_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val < r + W'.val ∧
      r + W.val ≠ r + W'.val :=
  ⟨h.center_index_lt, h.center_index_ne⟩

/--
Boundary-sign pair surface with explicit center-index separation.

This is the caller-facing form for local pulse comparison: both endpoints carry
their nonpositive-positive-nonpositive sign windows, and the center indices are
strictly ordered and distinct.
-/
theorem SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                r + W.val < r + W'.val ∧
                  r + W.val ≠ r + W'.val := by
  rcases h.indexed_boundary_pair_surface with
    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt,
    h.center_index_ne⟩

/--
First interference theorem for a forward pair comparison state.

The right positive center cannot be exactly the successor of the left positive
center.  If it were, the right endpoint's previous nonpositive boundary would
coincide with the left endpoint's positive center.
-/
theorem SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W'.val ≠ W.val + 1 := by
  intro hsucc
  rcases h.boundary_sign_pair_surface with
    ⟨_, hcenterL, _, hprevR, _, _, _⟩
  have hidx : r + (W'.val - 1) = r + W.val := by
    omega
  have hle : SourcePressureMarginInt n k (r + W.val) ≤ 0 := by
    simpa [hidx] using hprevR
  exact (not_le_of_gt hcenterL) hle

/--
The right positive center is separated from the left positive center by more
than one value step.

This is the value-level form of the first interference theorem.
-/
theorem SourcePressureForwardPairComparisonState.left_succ_lt_right_val
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W.val + 1 < W'.val := by
  have hlt : W.val < W'.val := h.val_lt
  have hne : W'.val ≠ W.val + 1 := h.not_right_val_eq_left_succ
  omega

/--
Index-level form of the first interference theorem.

The right positive center lies strictly beyond the left center's next boundary
index.  This is the margin-index version of `left_succ_lt_right_val`.
-/
theorem SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 < r + W'.val := by
  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
  omega

/--
Syntactic variant of `left_next_index_lt_right_center_index` using
`r + (W.val + 1)` as the left boundary expression.
-/
theorem SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + (W.val + 1) < r + W'.val := by
  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
  omega

/--
Boundary-sign pair surface bundled with the first interference gap.

This strengthens `indexed_boundary_separation_surface` by adding the fact that
the left endpoint's next boundary index is still strictly before the right
positive center.  It is a local pair-comparison statement, not a global
coverage or uniqueness claim.
-/
theorem SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                r + W.val < r + W'.val ∧
                  r + W.val ≠ r + W'.val ∧
                    r + W.val + 1 < r + W'.val := by
  rcases h.indexed_boundary_separation_surface with
    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt, hne⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
    hlt, hne, h.left_next_index_lt_right_center_index⟩

/--
Projection from `indexed_boundary_gap_surface`: the left next boundary index is
strictly before the right positive center.
-/
theorem SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 < r + W'.val := by
  rcases h.indexed_boundary_gap_surface with
    ⟨_, _, _, _, _, _, _, _, hgap⟩
  exact hgap

/--
Compact caller-facing projection for the next interference layer: the left next
boundary is nonpositive and still lies strictly before the right positive
center.
-/
theorem SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      r + W.val + 1 < r + W'.val := by
  rcases h.indexed_boundary_gap_surface with
    ⟨_, _, hnextL, _, _, _, _, _, hgap⟩
  exact ⟨hnextL, hgap⟩

/--
Compact left-next interference surface for local window comparison.

It records the left positive center, the immediate nonpositive boundary after
that center, the right positive center, and the strict index gap from the left
next boundary to the right center.
-/
theorem SourcePressureForwardPairComparisonState.left_next_interference_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          r + W.val + 1 < r + W'.val := by
  rcases h.indexed_boundary_gap_surface with
    ⟨_, hcenterL, hnextL, _, hcenterR, _, _, _, hgap⟩
  exact ⟨hcenterL, hnextL, hcenterR, hgap⟩

/--
Index corridor between the left next boundary and the right previous boundary.

The first interference theorem gives `W.val + 1 < W'.val`; at the addressed
index level this means the left next boundary is no later than the right
previous boundary.
-/
theorem SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 ≤ r + (W'.val - 1) := by
  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
  omega

/--
Boundary corridor surface for a forward pair comparison state.

Both corridor endpoints are nonpositive boundary indices, and the left next
boundary lies no later than the right previous boundary.
-/
theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        r + W.val + 1 ≤ r + (W'.val - 1) := by
  rcases h.indexed_boundary_gap_surface with
    ⟨_, _, hnextL, hprevR, _, _, _, _, _⟩
  exact ⟨hnextL, hprevR, h.left_next_boundary_le_right_previous_boundary⟩

/--
The boundary corridor is either a contact corridor or a genuine gap corridor.

This is the index-level split used by the next window-interference layer: the
left next boundary either coincides with the right previous boundary, or it lies
strictly before it.
-/
theorem SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 = r + (W'.val - 1) ∨
      r + W.val + 1 < r + (W'.val - 1) := by
  have hle : r + W.val + 1 ≤ r + (W'.val - 1) :=
    h.left_next_boundary_le_right_previous_boundary
  omega

/--
Sign-bundled contact-or-gap split for the boundary corridor.

Both corridor endpoints are nonpositive, and the corridor is either the contact
case where those endpoints coincide, or the genuine gap case where the left
next boundary lies strictly before the right previous boundary.
-/
theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        (r + W.val + 1 = r + (W'.val - 1) ∨
          r + W.val + 1 < r + (W'.val - 1)) := by
  rcases h.boundary_corridor_surface with ⟨hnextL, hprevR, _hle⟩
  exact ⟨hnextL, hprevR, h.boundary_corridor_eq_or_lt⟩

/--
Contact-corridor projection.

When the corridor endpoints coincide, the shared boundary is represented by
two syntactic index expressions, and both are nonpositive.  The contact equality
is accepted as branch data; this theorem only projects the endpoint signs.
-/
theorem SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (_hcontact : r + W.val + 1 = r + (W'.val - 1)) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 := by
  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, _hsplit⟩
  exact ⟨hnextL, hprevR⟩

/--
Strict-gap corridor projection.

In the genuine gap branch, both corridor endpoints remain nonpositive and the
left endpoint is strictly before the right endpoint.  This does not assert
anything about every interior index of the corridor.
-/
theorem SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hgap : r + W.val + 1 < r + (W'.val - 1)) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        r + W.val + 1 < r + (W'.val - 1) := by
  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, _hsplit⟩
  exact ⟨hnextL, hprevR, hgap⟩

set_option linter.style.longLine false in
/--
Value-level form of the corridor split.

The right center is either exactly two value steps after the left center, or it
is strictly farther away.  This mirrors `boundary_corridor_eq_or_lt` before the
common offset `r` is added and before right-previous indexing is formed.
-/
theorem SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W'.val = W.val + 2 ∨ W.val + 2 < W'.val := by
  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
  omega

/--
Constructor from the forward box comparison state to the pair-comparison-facing
state.

All additional fields are projections already stored in the forward state.
-/
theorem SourcePressureForwardBoxComparisonState.to_pairComparisonState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardBoxComparisonState L W W') :
    SourcePressureForwardPairComparisonState L W W' :=
  ⟨h, h.adjacentPair, h.left_box, h.right_box⟩

/--
Constructor from a sorted oriented neighbor box to the named forward comparison
state.

The sortedness hypothesis is where the value comparison and reverse-orientation
exclusion enter; the box alone intentionally remains weaker.
-/
theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    SourcePressureForwardBoxComparisonState L W W' :=
  ⟨hbox, hbox.val_lt_of_sorted hsorted,
    hbox.not_reverse_box_of_sorted hsorted⟩

/--
Package an oriented neighbor diagnostic into the two-endpoint box state.

The oriented diagnostic supplies the endpoint sign patterns through
`sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs` and
`sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs`.
The finite height and jump boxes are supplied pointwise by
`sourcePressureMarginInt_bounds_window` and
`sourcePressureNetDropInt_bounds_window`.
-/
theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
    SourcePressureOrientedNeighborBoxState L W W' := by
  rcases h with
    ⟨hin, hdiag, hentry, haddr, hexit, hentry', haddr', hexit'⟩
  let hD : SourcePressureOrientedNeighborDiagnosticState L W W' :=
    ⟨hin, hdiag, hentry, haddr, hexit, hentry', haddr', hexit'⟩
  rcases
    sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
      hD with
    ⟨hprev, hcenter, haddrLeft, hnext⟩
  rcases
    sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
      hD with
    ⟨hprev', hcenter', haddrRight, hnext'⟩
  have hboxLeft : SourcePressureBeamCenteredLocalPulseBox n k r L W :=
    ⟨sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin,
      hprev,
      hcenter,
      haddrLeft,
      hnext,
      sourcePressureMarginInt_bounds_window n k (r + (W.val - 1)),
      sourcePressureMarginInt_bounds_window n k (r + W.val),
      sourcePressureMarginInt_bounds_window n k (r + W.val + 1),
      sourcePressureNetDropInt_bounds_window n k r (W.val - 1),
      sourcePressureNetDropInt_bounds_window n k r W.val⟩
  have hboxRight : SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
    ⟨sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin,
      hprev',
      hcenter',
      haddrRight,
      hnext',
      sourcePressureMarginInt_bounds_window n k (r + (W'.val - 1)),
      sourcePressureMarginInt_bounds_window n k (r + W'.val),
      sourcePressureMarginInt_bounds_window n k (r + W'.val + 1),
      sourcePressureNetDropInt_bounds_window n k r (W'.val - 1),
      sourcePressureNetDropInt_bounds_window n k r W'.val⟩
  exact ⟨hD, hboxLeft, hboxRight⟩

/--
Recovered adjacent state enters the oriented neighbor diagnostic state.

This fills the first recovered-branch Gap slot:

```text
RecoveredAdjacent
  -- attachAdjacentDiagnosis + attachForwardOrientation -->
OrientedNeighborDiagnostic
```

The recovered state already stores both ingredients needed here:

* the ordered adjacent-pair address `hin`;
* the named pair-local recovered diagnostic `hrec`.

Opening `hrec` gives the reversed-before witness and budget bound required by
`SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered`.  The endpoint
Beam diagnostics are then supplied by
`sourcePressureOrientedNeighborDiagnosticState_of_forward`.

No canonical pair is selected beyond the existential pair already stored in
the recovered state, and no coverage, aggregation, transport, or convergence
is claimed.
-/
theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    ∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W' := by
  rcases h with ⟨A, B, hin, hrec⟩
  rcases hrec with ⟨hrev, hbudget, _hneg, _hlen⟩
  let hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
    SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
  exact
    ⟨A, B,
      sourcePressureOrientedNeighborDiagnosticState_of_forward hin hdiag⟩

/--
Failure resolution splits into either an oriented neighbor diagnostic or an
adjacent-overlap state.

This is the mnemonic automaton branch after the recovered branch has been
upgraded to oriented local diagnostics:

```text
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ AdjacentOverlap
```

The recovered side uses
`sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState`.
The overlap side is kept as the explicit obstruction state.  No overlap repair,
coverage, aggregation, transport, or convergence is claimed.
-/
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      SourcePressureAdjacentOverlapState L := by
  rcases sourcePressureFailureResolutionState_cases h with hrec | hoverlap
  · exact Or.inl
      (sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
        hrec)
  · exact Or.inr hoverlap

/--
Adjacent-overlap state exposes a concrete adjacent pair carrying the pair-level
overlap obstruction.

This refines the mnemonic overlap state from list-level obstruction to the
addressed pair that witnesses it.  It still does not repair the overlap or
select a canonical obstructing pair; the pair is merely the existential pair
provided by the existing obstruction theorem.
-/
theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureAdjacentOverlapState L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction h

/--
Failure resolution splits into either an oriented neighbor diagnostic or a
concrete adjacent pair-level overlap obstruction.

This is the pair-refined version of
`sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState`.
The recovered branch reaches the Beam-facing oriented diagnostic state; the
overlap branch now exposes the addressed obstructing adjacent pair.
-/
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  rcases
    sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
      h with hdiag | hoverlap
  · exact Or.inl hdiag
  · exact Or.inr
      (sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
        hoverlap)

/--
Sorted failure reaches the same refined diagnostic/obstruction split.

This theorem composes the sorted-failure entry point with the existing
failure-resolution transition, then exposes the pair-refined exit:

```text
SortedFailure
  -> OrientedNeighborDiagnostic
   ∨ PairOverlapObstruction
```

It is intentionally only a lift through the state automaton.  It does not add
repair, canonical selection, global coverage, or propagation beyond the
adjacent pair supplied by the obstruction branch.
-/
theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
    (sourcePressureSortedFailureState_to_failureResolutionState h)

/--
Beam seed reaches the same refined diagnostic/obstruction split.

This theorem exposes the Beam-seed entry point as a direct caller-facing split:

```text
BeamSeed
  -> OrientedNeighborDiagnostic
   ∨ PairOverlapObstruction
```

It is only the already-proved `BeamSeed -> FailureResolution` transition
followed by the pair-refined failure-resolution split.  No stronger accounting,
repair, propagation, or convergence statement is introduced here.
-/
theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
    (sourcePressureBeamSeedState_to_failureResolutionState h)

/--
Failure resolution splits into either a two-endpoint oriented neighbor box or a
concrete pair-level overlap obstruction.

This is the boxed version of
`sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap`.
Only the diagnostic branch is strengthened, by packaging state `D` into
`SourcePressureOrientedNeighborBoxState`.  The overlap branch is kept as the
same concrete adjacent-pair obstruction.
-/
theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  rcases
    sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
      h with hdiag | hoverlap
  · rcases hdiag with ⟨W, W', hD⟩
    exact Or.inl
      ⟨W, W',
        sourcePressureOrientedNeighborDiagnosticState_to_boxState hD⟩
  · exact Or.inr hoverlap

/--
Sorted failure reaches the boxed diagnostic/obstruction split.

This lifts the sorted-failure entry point through failure resolution and then
through the boxed diagnostic branch.  It remains a local state-automaton
wrapper and does not add coverage, propagation, overlap repair, or convergence.
-/
theorem sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
    (sourcePressureSortedFailureState_to_failureResolutionState h)

/--
Beam seed reaches the boxed diagnostic/obstruction split.

This is the Beam-facing entry point for the same boxed split:

```text
BeamSeed
  -> OrientedNeighborBox
   ∨ PairOverlapObstruction
```
-/
theorem sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
    (sourcePressureBeamSeedState_to_failureResolutionState h)

/--
Failure resolution reaches a comparison-ready split under sortedness.

The boxed branch is strengthened from a raw two-endpoint box to a forward
comparison package:

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> not Box(W',W)
```

The pair-overlap obstruction branch is left unchanged.  This theorem is a
local routing surface for the next comparison layer; it does not repair
overlap, choose a canonical pair, or assert global coverage.
-/
theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W' ∧
        W.val < W'.val ∧
          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  rcases
    sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap h
      with hbox | hoverlap
  · rcases hbox with ⟨W, W', hbox⟩
    exact Or.inl
      ⟨W, W', hbox, hbox.val_lt_of_sorted hsorted,
        hbox.not_reverse_box_of_sorted hsorted⟩
  · exact Or.inr hoverlap

/--
Sorted failure reaches the comparison-ready boxed/overlap split.

This is the sorted-failure entry point for the same forward-comparison surface
provided by
`sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap`.
-/
theorem sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W' ∧
        W.val < W'.val ∧
          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)

/--
Beam seed reaches the comparison-ready boxed/overlap split.

This is the Beam-facing entry point:

```text
BeamSeed + sorted(L)
  -> ForwardBoxComparison
   ∨ PairOverlapObstruction
```

The sortedness hypothesis is explicit because the forward value comparison is
not a consequence of the seed state alone.
-/
theorem sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W' ∧
        W.val < W'.val ∧
          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

/--
Failure resolution reaches the named forward-comparison state or a concrete
pair-overlap obstruction.

This is the named-state wrapper over
`sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap`.
It removes tuple noise for callers that want to pass the forward branch into a
pair-comparison theorem as one state object.
-/
theorem sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureForwardBoxComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  rcases
    sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
      hsorted h with hforward | hoverlap
  · rcases hforward with ⟨W, W', hbox, hlt, hnrev⟩
    exact Or.inl ⟨W, W', hbox, hlt, hnrev⟩
  · exact Or.inr hoverlap

/--
Sorted failure reaches the named forward-comparison state or a concrete
pair-overlap obstruction.
-/
theorem sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureForwardBoxComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)

/--
Beam seed reaches the named forward-comparison state or a concrete pair-overlap
obstruction.

This is the Beam-facing named split that later pair-comparison layers should
prefer over the raw tuple form.
-/
theorem sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureForwardBoxComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

/--
Failure resolution reaches the forward pair-comparison state or a concrete
pair-overlap obstruction.

This is the pair-comparison-facing lift of
`sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap`.
The forward branch is converted by
`SourcePressureForwardBoxComparisonState.to_pairComparisonState`; the
obstruction branch is unchanged.
-/
theorem sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureForwardPairComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  rcases
    sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
      hsorted h with hforward | hoverlap
  · rcases hforward with ⟨W, W', hFBC⟩
    exact Or.inl ⟨W, W', hFBC.to_pairComparisonState⟩
  · exact Or.inr hoverlap

/--
Sorted failure reaches the forward pair-comparison state or a concrete
pair-overlap obstruction.
-/
theorem sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureForwardPairComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)

/--
Beam seed reaches the forward pair-comparison state or a concrete pair-overlap
obstruction.

This is the Beam-facing pair-comparison entry point produced by the current
state ladder.
-/
theorem sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureForwardPairComparisonState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
  sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

end DkMath.Collatz
