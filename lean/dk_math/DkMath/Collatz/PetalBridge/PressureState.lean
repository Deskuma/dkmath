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

end DkMath.Collatz
