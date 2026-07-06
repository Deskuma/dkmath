/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureAutomaton

#print "file: DkMath.Collatz.PetalBridge.PressureBeam"

namespace DkMath.Collatz

/-
Checkpoint 201: Beam-facing pressure boundary.

This file is deliberately above `PressureAutomaton`:

```text
PressureAutomaton
  <- PressureBeam
```

The lower files already own the local machinery:

* `PressureDecay` owns local margin/net-drop transitions;
* `PressureFrontier` owns local-island and interval-pulse production;
* `PressureAccounting` owns explicit witness-list accounting;
* `PressureAutomaton` owns the local failure-resolution state.

`PressureBeam` is the future home for Beam/time/orbit propagation of those
local automaton states.  This checkpoint only creates the boundary and the
first Beam-facing seed name.  It does not prove propagation, convergence,
coverage, aggregation, overlap repair, uniqueness, maximality, sorting, or
disjointness between multiple recovered families.
-/

/--
Beam-facing seed state for a local pressure witness list.

At this stage a Beam seed is exactly the local failure-resolution state already
provided by `PressureAutomaton`.  The new name marks the handoff point from
local automaton analysis to future Beam/time/orbit transport.

This is intentionally only an alias-like predicate.  It does not assert that
the seed propagates, covers a global interval, aggregates with other seeds, or
repairs overlap.
-/
def SourcePressureBeamSeed
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureFailureResolution L

/--
Sorted-before failure produces a Beam seed.

This is only the Beam-facing name for the automaton entry theorem
`sourcePressureFailureResolution_of_sortedBeforeFailure`.  It creates no new
propagation principle.
-/
theorem sourcePressureBeamSeed_of_sortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureBeamSeed L :=
  sourcePressureFailureResolution_of_sortedBeforeFailure h

/--
If adjacent overlap is excluded, a Beam seed exposes a recovered adjacent-pair
diagnostic.

This is still pair-local.  It does not aggregate recovered diagnostics across a
Beam and does not turn no-overlap into a global disjointness theorem.
-/
theorem sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
          A B :=
  sourcePressureFailureResolution_recovered_of_noAdjacentOverlap h hno

/--
Depth-indexed Beam target for local pressure.

This is the first explicit Beam-facing target axis.  It is deliberately the
pressure-depth axis `(r + j)`, because that is the native axis of the local
margin/net-drop machinery below this file.  The predicate only names a target
at one explicit relative pressure depth; it does not assert that a Beam seed
reaches the target, that targets cover a range, or that targets aggregate.
-/
def SourcePressureBeamDepthTarget
    (n : OddNat) (k r j : ℕ) : Prop :=
  IsSourcePressureDepth n k r j

/--
Beam depth targets are exactly positive source-pressure margins.

This is only the Beam-facing spelling of
`isSourcePressureDepth_iff_margin_pos`.  It is not a transport theorem from a
Beam seed to a target depth.
-/
theorem sourcePressureBeamDepthTarget_iff_margin_pos
    (n : OddNat) (k r j : ℕ) :
    SourcePressureBeamDepthTarget n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) :=
  isSourcePressureDepth_iff_margin_pos n k r j

/--
Construct a Beam depth target from positive source-pressure margin.

This is the True Beam constructor side of
`sourcePressureBeamDepthTarget_iff_margin_pos`.  It remains local to one
explicit depth and does not connect any Beam seed to that depth.
-/
theorem sourcePressureBeamDepthTarget_of_margin_pos
    (n : OddNat) (k r j : ℕ)
    (h : 0 < SourcePressureMarginInt n k (r + j)) :
    SourcePressureBeamDepthTarget n k r j :=
  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).2 h

/--
Project positive source-pressure margin from a Beam depth target.

This is the True Beam projection side of
`sourcePressureBeamDepthTarget_iff_margin_pos`.  It is not a propagation
result; it only opens the target predicate at the same explicit depth.
-/
theorem sourcePressureMargin_pos_of_beamDepthTarget
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureBeamDepthTarget n k r j) :
    0 < SourcePressureMarginInt n k (r + j) :=
  (sourcePressureBeamDepthTarget_iff_margin_pos n k r j).1 h

/--
An explicit Beam seed witness list contains a witness at relative depth `j`.

`SourcePressureLocalIslandWitness` is a subtype
`{ j : ℕ // SourcePressureLocalIsland n k r j }`, so the actual depth field is
`W.val`.  This relation is the first seed-to-depth connector.  It only says
that the supplied list contains an exact-depth witness; it does not claim that
the list is complete, sorted, maximal, or globally covering.
-/
def SourcePressureBeamSeedContainsDepth
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  ∃ W ∈ L, W.val = j

/--
If a supplied Beam seed witness list contains an exact-depth local-island
witness, then that depth is a Beam depth target.

This is not a real propagation theorem from `SourcePressureBeamSeed L`.
The proof uses only the explicit containment relation and the local-island
proof carried by the witness.
-/
theorem sourcePressureBeamDepthTarget_of_seedContainsDepth
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hcontains : SourcePressureBeamSeedContainsDepth L j) :
    SourcePressureBeamDepthTarget n k r j := by
  rcases hcontains with ⟨W, _hmem, hdepth⟩
  subst hdepth
  exact W.property.2.1

/--
An addressed adjacent pair in a witness list exposes the left witness depth as
contained in that list.

This is a list-address projection.  It does not choose a canonical adjacent
pair and does not aggregate over all adjacent pairs.
-/
theorem sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
    SourcePressureBeamSeedContainsDepth L A.val := by
  induction L generalizing A B with
  | nil =>
      exact False.elim hin
  | cons W1 rest ih =>
      cases rest with
      | nil =>
          exact False.elim hin
      | cons W2 rest =>
          rcases hin with hhead | htail
          · rcases hhead with ⟨hA, _hB⟩
            exact ⟨A, by simp [hA], rfl⟩
          · rcases ih htail with ⟨W, hmem, hdepth⟩
            exact ⟨W, by simp [hmem], hdepth⟩

/--
An adjacent-overlap obstruction in a witness list still exposes at least one
explicit witness depth from that list.

This is not overlap repair.  It only records that the obstruction branch is
also list-addressed, so an existential depth can be extracted.
-/
theorem exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ j, SourcePressureBeamSeedContainsDepth L j := by
  induction L with
  | nil =>
      exact False.elim hobs
  | cons W1 rest ih =>
      cases rest with
      | nil =>
          exact False.elim hobs
      | cons W2 rest =>
          rcases hobs with _hhead | htail
          · exact ⟨W1.val, W1, by simp, rfl⟩
          · rcases ih htail with ⟨j, W, hmem, hdepth⟩
            exact ⟨j, W, by simp [hmem], hdepth⟩

/--
A raw Beam seed contains at least one explicit witness depth.

This is the first existential target-extraction fact from the Beam seed state.
It is still not arbitrary target transport: the depth is produced
existentially from the addressed recovered or overlap branch.
-/
theorem exists_sourcePressureBeamSeedContainsDepth_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamSeedContainsDepth L j := by
  unfold SourcePressureBeamSeed at hseed
  unfold SourcePressureFailureResolution at hseed
  rcases hseed with hrecovered | hobs
  · rcases hrecovered with ⟨A, B, hin, _hdiag⟩
    exact ⟨A.val, sourcePressureBeamSeedContainsDepth_of_adjacentPairInList_left hin⟩
  · exact exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction hobs

/--
A raw Beam seed produces some Beam depth target.

The target depth is existentially extracted from the seed's addressed witness
data.  This theorem deliberately does not say that an arbitrary depth is a
target.
-/
theorem exists_sourcePressureBeamDepthTarget_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamDepthTarget n k r j := by
  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
    ⟨j, hcontains⟩
  exact ⟨j, sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains⟩

/--
A raw Beam seed produces an explicit contained depth together with the
corresponding Beam depth target.

This pairs the list-address relation and the target relation for the same
existential depth.
-/
theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamSeedContainsDepth L j ∧
        SourcePressureBeamDepthTarget n k r j := by
  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
    ⟨j, hcontains⟩
  exact ⟨j, hcontains, sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains⟩

/--
Named addressed carrier for a Beam depth target selected from a supplied seed
witness list.

This is packaging, not new propagation.  The carrier remembers both pieces of
data at the same explicit depth `j`:

* `L` contains a local-island witness whose depth is exactly `j`;
* `j` is a Beam depth target.

It does not choose a canonical target, transport arbitrary external depths,
aggregate multiple diagnostics, repair overlap, or claim global coverage.
-/
def SourcePressureBeamAddressedDepthTarget
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  SourcePressureBeamSeedContainsDepth L j ∧
    SourcePressureBeamDepthTarget n k r j

/--
Project the list-address containment from an addressed Beam depth target.
-/
theorem sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureBeamSeedContainsDepth L j :=
  h.1

/--
Project the Beam target fact from an addressed Beam depth target.
-/
theorem sourcePressureBeamDepthTarget_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureBeamDepthTarget n k r j :=
  h.2

/--
Construct an addressed Beam depth target from its two local components.
-/
theorem sourcePressureBeamAddressedDepthTarget_mk
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hcontains : SourcePressureBeamSeedContainsDepth L j)
    (htarget : SourcePressureBeamDepthTarget n k r j) :
    SourcePressureBeamAddressedDepthTarget L j :=
  ⟨hcontains, htarget⟩

/--
A raw Beam seed produces some addressed Beam depth target.

This is the named-carrier form of
`exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed`.  The depth is
still existentially selected from the supplied witness list; no arbitrary depth
transport or canonical selection is introduced.
-/
theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, SourcePressureBeamAddressedDepthTarget L j := by
  rcases exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed hseed with
    ⟨j, hcontains, htarget⟩
  exact ⟨j, sourcePressureBeamAddressedDepthTarget_mk hcontains htarget⟩

/--
An addressed Beam depth target exposes positive source-pressure margin.

This is only projection composition through the target component.  It is not
transport, propagation, or a coverage theorem.
-/
theorem sourcePressureMargin_pos_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j) :=
  sourcePressureMargin_pos_of_beamDepthTarget n k r j
    (sourcePressureBeamDepthTarget_of_addressedDepthTarget h)

/--
A raw Beam seed existentially exposes a positive source-pressure margin.

The depth is selected through the addressed carrier extracted from the seed.
This is not arbitrary margin positivity and does not propagate the Beam to a
new depth.
-/
theorem exists_sourcePressureMargin_pos_of_beamSeed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, 0 < SourcePressureMarginInt n k (r + j) := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddressed⟩
  exact ⟨j, sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩

/--
A raw Beam seed produces an addressed target together with positive margin at
the same extracted depth.

This keeps the address and the margin proof paired.  It is still an
existential projection from the supplied seed data, not a canonical choice.
-/
theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        0 < SourcePressureMarginInt n k (r + j) := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddressed⟩
  exact ⟨j, haddressed, sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩

/--
A raw Beam seed produces a Beam depth target together with positive margin at
the same extracted depth.

This is a thinner package for callers that do not need the list-address
component.  It does not state positivity for arbitrary external depths.
-/
theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamDepthTarget n k r j ∧
        0 < SourcePressureMarginInt n k (r + j) := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddressed⟩
  exact
    ⟨j,
      sourcePressureBeamDepthTarget_of_addressedDepthTarget haddressed,
      sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩

/--
An addressed Beam depth target opens the local source-pressure margin
transition equation at the same depth.

This is only the Beam-facing spelling of the local `PressureDecay` transition
identity.  The addressed target hypothesis is intentionally unused by the
algebraic equation; it documents that the equation is being read at a depth
selected by the supplied witness list.  No time/orbit propagation is asserted.
-/
theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_h : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j :=
  sourcePressureMargin_next_eq_current_add_netDrop n k r j

/--
A raw Beam seed existentially exposes an addressed target together with the
local margin transition equation at that same selected depth.

The selected depth is existential.  This is not a statement that the transition
at an arbitrary external depth belongs to the seed.
-/
theorem exists_sourcePressureMargin_transition_of_beamSeed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        SourcePressureMarginInt n k (r + j + 1) =
          SourcePressureMarginInt n k (r + j) +
            SourcePressureNetDropInt n k r j := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddressed⟩
  exact
    ⟨j,
      haddressed,
      sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
        haddressed⟩

/--
Local True Beam sign preservation at an addressed depth.

If the current addressed margin is positive and the local net drop is
nonnegative, then the next adjacent margin is still positive.  This is a local
sign-reading theorem over the already addressed pressure-depth edge; it does
not propagate along time or choose any new target.
-/
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop : 0 ≤ SourcePressureNetDropInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hcur := sourcePressureMargin_pos_of_addressedDepthTarget haddr
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega

/--
A raw Beam seed existentially exposes an addressed depth whose next margin is
positive, provided every addressed depth in the seed has nonnegative net drop.

The quantifier over `j` is restricted by `SourcePressureBeamAddressedDepthTarget
L j`.  This is not arbitrary next-margin positivity and not propagation.
-/
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L)
    (hdrop :
      ∀ j,
        SourcePressureBeamAddressedDepthTarget L j →
          0 ≤ SourcePressureNetDropInt n k r j) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        0 < SourcePressureMarginInt n k (r + j + 1) := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddr⟩
  exact
    ⟨j,
      haddr,
      sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
        haddr (hdrop j haddr)⟩

/--
Local False Beam drop condition at an addressed depth.

If the local net drop is at most the negative of the current positive margin,
then the next adjacent margin is nonpositive.  This records a genuine local
fall-out condition, but still only at the addressed pressure-depth edge.
-/
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop :
      SourcePressureNetDropInt n k r j ≤
        -SourcePressureMarginInt n k (r + j)) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega

/--
Sharp local True Beam condition at an addressed depth.

The next adjacent margin is positive whenever the net drop is larger than the
negative of the current addressed margin.  This is the sharp form of the
nonnegative-net-drop theorem: the net drop may be negative, as long as it does
not cross the current positive margin through zero.
-/
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop :
      -SourcePressureMarginInt n k (r + j) <
        SourcePressureNetDropInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega

/--
Direct local sum form of the sharp True Beam condition.

This is often the most convenient shape after opening the local transition
equation.
-/
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hsum :
      0 <
        SourcePressureMarginInt n k (r + j) +
          SourcePressureNetDropInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  exact hsum

/--
A raw Beam seed existentially exposes an addressed depth whose next margin is
positive under the sharp addressed net-drop condition.

The net-drop hypothesis is still restricted to addressed depths selected from
the seed witness list.
-/
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L)
    (hdrop :
      ∀ j,
        SourcePressureBeamAddressedDepthTarget L j →
          -SourcePressureMarginInt n k (r + j) <
            SourcePressureNetDropInt n k r j) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        0 < SourcePressureMarginInt n k (r + j + 1) := by
  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
    ⟨j, haddr⟩
  exact
    ⟨j,
      haddr,
      sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
        haddr (hdrop j haddr)⟩

/--
Sharp local True Beam classifier at an addressed depth.

This is a local arithmetic classifier for the next sign at the addressed edge:
after opening the transition equation, next positivity is exactly
`-current < netDrop`.
-/
theorem sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      -SourcePressureMarginInt n k (r + j) <
        SourcePressureNetDropInt n k r j := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega

/--
Sharp local False Beam classifier at an addressed depth.

The next adjacent margin is nonpositive exactly when the net drop is at most
the negative of the current margin.
-/
theorem sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourcePressureNetDropInt n k r j ≤
        -SourcePressureMarginInt n k (r + j) := by
  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    haddr]
  omega

end DkMath.Collatz
