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

end DkMath.Collatz
