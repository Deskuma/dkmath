/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureAutomaton

#print "file: DkMath.Collatz.PetalBridge.PressureBeam.Core"

namespace DkMath.Collatz

/-
Checkpoint 201 / 225: Beam-facing pressure boundary core.

This file is deliberately above `PressureAutomaton`:

```text
PressureAutomaton
  <- PressureBeam.Core
```

The lower files already own the local machinery:

* `PressureDecay` owns local margin/net-drop transitions;
* `PressureFrontier` owns local-island and interval-pulse production;
* `PressureAccounting` owns explicit witness-list accounting;
* `PressureAutomaton` owns the local failure-resolution state.

`PressureBeam.Core` keeps the seed, addressed-depth, and mass-balance core for
Beam-facing pressure work.  Checkpoint 225 split the former monolithic
`PressureBeam.lean`; public theorem names and theorem statements are unchanged.
This core layer does not prove propagation, convergence, coverage, aggregation,
overlap repair, uniqueness, maximality, sorting, or disjointness between
multiple recovered families.
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

/--
Beam-facing expansion of the local net pressure drop at an addressed depth.

This is only the definition of `SourcePressureNetDropInt` read through the Beam
addressing API.  The addressed hypothesis is intentionally unused by the
arithmetic identity; it records that the equation is being used at a
Beam-selected pressure-depth edge.
-/
theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureNetDropInt n k r j =
      SourceRetentionDropInt n k r j -
        2 * SourceContinuationDropInt n k r j := by
  rfl

/--
True Beam classifier with net drop expanded into retention and continuation
drops.

At an addressed edge, the next margin is positive exactly when the expanded
quantity `retentionDrop - 2 * continuationDrop` is larger than `-current`.
-/
theorem sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      -SourcePressureMarginInt n k (r + j) <
        SourceRetentionDropInt n k r j -
          2 * SourceContinuationDropInt n k r j := by
  rw [sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
    haddr]
  rw [sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
    haddr]

/--
False Beam classifier with net drop expanded into retention and continuation
drops.

At an addressed edge, the next margin is nonpositive exactly when the expanded
quantity `retentionDrop - 2 * continuationDrop` is at most `-current`.
-/
theorem sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourceRetentionDropInt n k r j -
          2 * SourceContinuationDropInt n k r j
        ≤ -SourcePressureMarginInt n k (r + j) := by
  rw [sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
    haddr]
  rw [sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
    haddr]

/--
Normalized True Beam count inequality at an addressed depth.

The local True classifier can be read as a comparison between twice the
continuation drop and the retention drop plus the current margin.
-/
theorem sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      2 * SourceContinuationDropInt n k r j <
        SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j) := by
  rw [sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
    haddr]
  omega

/--
Normalized False Beam count inequality at an addressed depth.

The next margin is nonpositive exactly when the retention drop plus the
current margin is at most twice the continuation drop.
-/
theorem sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j)
        ≤ 2 * SourceContinuationDropInt n k r j := by
  rw [sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
    haddr]
  omega

/--
One-way True Beam wrapper for the normalized count inequality.
-/
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      2 * SourceContinuationDropInt n k r j <
        SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j)) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hiff :=
    sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
      haddr
  exact hiff.2 hineq

/--
One-way False Beam wrapper for the normalized count inequality.
-/
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j)
        ≤ 2 * SourceContinuationDropInt n k r j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  have hiff :=
    sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
      haddr
  exact hiff.2 hineq

/--
Beam-facing expansion of the retention drop at an addressed depth.

This is definitionally the current retention mass minus the next retention
mass.  The addressed hypothesis is intentionally unused by the arithmetic
identity; it records that the expansion is being read at a Beam-selected edge.
-/
theorem sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourceRetentionDropInt n k r j =
      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
        (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
  rfl

/--
Beam-facing expansion of the continuation drop at an addressed depth.

This is definitionally the current continuation-sibling mass minus the next
continuation-sibling mass.
-/
theorem sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourceContinuationDropInt n k r j =
      (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
        (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
  rfl

/--
True Beam classifier with drops opened into mass differences.

At an addressed edge, the next margin is positive exactly when twice the
continuation mass loss is smaller than the retention mass loss plus the
current margin.
-/
theorem sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      2 *
          ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
            (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) <
        ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
            (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
          SourcePressureMarginInt n k (r + j) := by
  rw [sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
    haddr]
  rw [sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
  rw [sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]

/--
False Beam classifier with drops opened into mass differences.

At an addressed edge, the next margin is nonpositive exactly when the retention
mass loss plus the current margin is at most twice the continuation mass loss.
-/
theorem sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
        SourcePressureMarginInt n k (r + j) ≤
          2 *
            ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
              (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) := by
  rw [sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
    haddr]
  rw [sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
  rw [sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]

/--
True Beam classifier in direct mass-balance form.

This is only the cp213 mass-difference classifier with the linear terms moved
across the inequality.  It does not propagate the addressed edge.
-/
theorem sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) <
        (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
          SourcePressureMarginInt n k (r + j) +
            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
  rw [sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
    haddr]
  omega

/--
False Beam classifier in direct mass-balance form.

This is the nonpositive companion to the True Beam mass-balance classifier.
-/
theorem sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
          SourcePressureMarginInt n k (r + j) +
            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) ≤
        2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
  rw [sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
    haddr]
  omega

/--
One-way True Beam wrapper for the direct mass-balance inequality.
-/
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) <
        (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
          SourcePressureMarginInt n k (r + j) +
            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hiff :=
    sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget haddr
  exact hiff.2 hineq

/--
One-way False Beam wrapper for the direct mass-balance inequality.
-/
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
          SourcePressureMarginInt n k (r + j) +
            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) ≤
        2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  have hiff :=
    sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget haddr
  exact hiff.2 hineq

/--
Left side of the source-pressure Beam mass-balance comparison.

This names the recurring expression
`2 * contNow + retNext`.  It is kept in this Beam layer because it packages the
local addressed-edge classifier, not a global pressure propagation principle.
-/
noncomputable def SourcePressureBeamMassBalanceLeftInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)

/--
Right side of the source-pressure Beam mass-balance comparison.

This names the recurring expression
`retNow + currentMargin + 2 * contNext`.
-/
noncomputable def SourcePressureBeamMassBalanceRightInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
    SourcePressureMarginInt n k (r + j) +
      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

/--
Expansion of the named left mass-balance side.
-/
theorem sourcePressureBeamMassBalanceLeftInt_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureBeamMassBalanceLeftInt n k r j =
      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
        (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
  rfl

/--
Expansion of the named right mass-balance side.
-/
theorem sourcePressureBeamMassBalanceRightInt_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureBeamMassBalanceRightInt n k r j =
      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
        SourcePressureMarginInt n k (r + j) +
          2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
  rfl

/--
True Beam classifier using the named mass-balance sides.
-/
theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      SourcePressureBeamMassBalanceLeftInt n k r j <
        SourcePressureBeamMassBalanceRightInt n k r j := by
  rw [sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
    haddr]
  rfl

/--
False Beam classifier using the named mass-balance sides.
-/
theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourcePressureBeamMassBalanceRightInt n k r j ≤
        SourcePressureBeamMassBalanceLeftInt n k r j := by
  rw [sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
    haddr]
  rfl

/--
One-way True Beam wrapper for the named mass-balance comparison.
-/
theorem sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      SourcePressureBeamMassBalanceLeftInt n k r j <
        SourcePressureBeamMassBalanceRightInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hiff := sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right haddr
  exact hiff.2 hineq

/--
One-way False Beam wrapper for the named mass-balance comparison.
-/
theorem sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hineq :
      SourcePressureBeamMassBalanceRightInt n k r j ≤
        SourcePressureBeamMassBalanceLeftInt n k r j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  have hiff := sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left haddr
  exact hiff.2 hineq

/--
Exact local relation between the next margin and the named mass-balance sides.

At an addressed Beam edge, the next margin is the right side minus the left
side.  This is stronger than the sign classifiers and explains why equality is
the zero boundary.
-/
theorem sourcePressureMargin_next_eq_massBalanceRight_sub_left
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureBeamMassBalanceRightInt n k r j -
        SourcePressureBeamMassBalanceLeftInt n k r j := by
  unfold SourcePressureBeamMassBalanceLeftInt
  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
  ring

/--
Boundary Beam classifier: the next margin is zero exactly on the equality
surface between the named mass-balance sides.
-/
theorem sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) = 0 ↔
      SourcePressureBeamMassBalanceLeftInt n k r j =
        SourcePressureBeamMassBalanceRightInt n k r j := by
  rw [sourcePressureMargin_next_eq_massBalanceRight_sub_left haddr]
  omega

/--
Boundary Beam wrapper: equality of the named mass-balance sides forces the next
margin to be zero.
-/
theorem sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hboundary :
      SourcePressureBeamMassBalanceLeftInt n k r j =
        SourcePressureBeamMassBalanceRightInt n k r j) :
    SourcePressureMarginInt n k (r + j + 1) = 0 := by
  have hiff :=
    sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right haddr
  exact hiff.2 hboundary

/--
False Beam boundary wrapper: equality of the named mass-balance sides is already
inside the nonpositive side.
-/
theorem sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hboundary :
      SourcePressureBeamMassBalanceLeftInt n k r j =
        SourcePressureBeamMassBalanceRightInt n k r j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
  have hzero :=
    sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr hboundary
  omega

/--
Boundary obstruction wrapper: equality of the named mass-balance sides rules out
the positive next-margin side.
-/
theorem not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hboundary :
      SourcePressureBeamMassBalanceLeftInt n k r j =
        SourcePressureBeamMassBalanceRightInt n k r j) :
    ¬ 0 < SourcePressureMarginInt n k (r + j + 1) := by
  have hzero :=
    sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr hboundary
  omega

/--
Strict False Beam classifier: the next margin is negative exactly when the
right mass-balance side is strictly smaller than the left side.
-/
theorem sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) < 0 ↔
      SourcePressureBeamMassBalanceRightInt n k r j <
        SourcePressureBeamMassBalanceLeftInt n k r j := by
  rw [sourcePressureMargin_next_eq_massBalanceRight_sub_left haddr]
  omega

/--
Local three-way Beam decision surface at an addressed depth.

This packages the useful information, not just the ambient linear-order
trichotomy: each mass-balance case is paired with the corresponding next-margin
sign.  It remains a local classifier for one addressed edge.
-/
theorem sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    (0 < SourcePressureMarginInt n k (r + j + 1) ∧
        SourcePressureBeamMassBalanceLeftInt n k r j <
          SourcePressureBeamMassBalanceRightInt n k r j) ∨
      (SourcePressureMarginInt n k (r + j + 1) = 0 ∧
          SourcePressureBeamMassBalanceLeftInt n k r j =
            SourcePressureBeamMassBalanceRightInt n k r j) ∨
        (SourcePressureMarginInt n k (r + j + 1) < 0 ∧
          SourcePressureBeamMassBalanceRightInt n k r j <
            SourcePressureBeamMassBalanceLeftInt n k r j) := by
  rcases lt_trichotomy
      (SourcePressureBeamMassBalanceLeftInt n k r j)
      (SourcePressureBeamMassBalanceRightInt n k r j) with hlt | heq | hgt
  · left
    exact ⟨sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right haddr hlt, hlt⟩
  · right
    left
    exact ⟨sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr heq, heq⟩
  · right
    right
    have hneg :=
      (sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left haddr).2 hgt
    exact ⟨hneg, hgt⟩

/-
Upstream inequality-source bridge.

Checkpoint 218 changes the question from "how do we classify an addressed
edge once `left` and `right` are known?" to "which upstream predicates can
supply `left < right`, equality, or the false-side comparison?"  The immediate
source is not the aggregate drift/accounting layer: those theorems speak about
finite intervals, sums, tails, or bounded witness lists.  The direct local
input is the sign-change layer from `PressureDecay`/`PressureFrontier`.

The lemmas below intentionally remain edge-local.  They do not transport an
arbitrary target, aggregate recovered intervals, repair overlap, choose a
canonical next target, or assert convergence.  They only say that an upstream
sign change at the same addressed edge feeds the already-closed Beam
mass-balance classifier.
-/

/--
An upstream upward sign change supplies the True Beam mass-balance inequality.

This is the first direct source of
`SourcePressureBeamMassBalanceLeftInt < SourcePressureBeamMassBalanceRightInt`.
The addressed target supplies the Beam reading of the edge; the sign-change
predicate supplies positivity of the next margin at that same edge.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hchange : SourcePressureSignChangeUp n k r j) :
    SourcePressureBeamMassBalanceLeftInt n k r j <
      SourcePressureBeamMassBalanceRightInt n k r j :=
  (sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right haddr).1
    hchange.2

/--
An upstream downward sign change supplies the False/Boundary Beam comparison.

The result is non-strict because `SourcePressureSignChangeDown` records that
the next margin is nonpositive.  The strict false branch is recovered by the
existing theorem `sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left`
when a strictly negative next margin is available.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hchange : SourcePressureSignChangeDown n k r j) :
    SourcePressureBeamMassBalanceRightInt n k r j ≤
      SourcePressureBeamMassBalanceLeftInt n k r j :=
  (sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left haddr).1
    hchange.2

/--
A local pressure island supplies the True Beam inequality on its left edge.

The address is deliberately for `j - 1`, the exact left edge produced by
`sourcePressureSignChangeUp_of_localIsland`.  This is not arbitrary target
transport.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIsland_left
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L (j - 1))
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureBeamMassBalanceLeftInt n k r (j - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (j - 1) :=
  sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp haddr
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

/--
A local pressure island supplies the False/Boundary Beam comparison on its
right edge.

The address is for the same right edge `j` as
`sourcePressureSignChangeDown_of_localIsland`.  The theorem remains local to
that edge and does not account for an entire island family.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_localIsland_right
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureBeamMassBalanceRightInt n k r j ≤
      SourcePressureBeamMassBalanceLeftInt n k r j :=
  sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown haddr
    (sourcePressureSignChangeDown_of_localIsland n k r j hisland)

/-
Interval-pulse exact-edge bridge.

Checkpoint 219 connects the interval-pulse address layer back into the Beam
classifier.  The important point is that the edge indices are not invented:

* left edge  = `A.start - 1`
* right edge = `A.start + A.len - 1`

`PressureFrontier` already stores sign-change facts at exactly these edges via
`sourcePressureIntervalPulseAddress_left_signChange` and
`sourcePressureIntervalPulseAddress_right_signChange`.  Therefore the Beam
bridge is only a local exact-edge composition through the cp218 sign-change
API.  It does not assert interval coverage, family aggregation, overlap repair,
or target transport.
-/

/--
An interval-pulse address supplies the True Beam mass-balance inequality at
its exact left edge.

The addressed target hypothesis is for `A.start - 1`, matching the edge stored
by `sourcePressureIntervalPulseAddress_left_signChange`.
-/
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (A : SourcePressureIntervalPulseAddress n k r)
    (haddr : SourcePressureBeamAddressedDepthTarget L (A.start - 1)) :
    SourcePressureBeamMassBalanceLeftInt n k r (A.start - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (A.start - 1) :=
  sourcePressureBeamMassBalanceLeft_lt_right_of_signChangeUp haddr
    (sourcePressureIntervalPulseAddress_left_signChange A)

/--
An interval-pulse address supplies the False/Boundary Beam comparison at its
exact right edge.

The addressed target hypothesis is for `A.start + A.len - 1`, matching the
edge stored by `sourcePressureIntervalPulseAddress_right_signChange`.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (A : SourcePressureIntervalPulseAddress n k r)
    (haddr :
      SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)) :
    SourcePressureBeamMassBalanceRightInt n k r (A.start + A.len - 1) ≤
      SourcePressureBeamMassBalanceLeftInt n k r (A.start + A.len - 1) :=
  sourcePressureBeamMassBalanceRight_le_left_of_signChangeDown haddr
    (sourcePressureIntervalPulseAddress_right_signChange A)

/--
An interval-pulse address supplies next-margin positivity at its exact left
edge.

This is a caller-friendly sign statement parallel to the mass-balance form.
It remains exact-edge only.
-/
theorem sourcePressureMargin_next_pos_of_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (A : SourcePressureIntervalPulseAddress n k r)
    (haddr : SourcePressureBeamAddressedDepthTarget L (A.start - 1)) :
    0 < SourcePressureMarginInt n k (r + (A.start - 1) + 1) :=
  sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right haddr
    (sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left A haddr)

/--
An interval-pulse address supplies next-margin nonpositivity at its exact right
edge.

This is the sign-form companion of
`sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right`.
-/
theorem sourcePressureMargin_next_nonpos_of_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (A : SourcePressureIntervalPulseAddress n k r)
    (haddr :
      SourcePressureBeamAddressedDepthTarget L (A.start + A.len - 1)) :
    SourcePressureMarginInt n k (r + (A.start + A.len - 1) + 1) ≤ 0 :=
  sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr
    (sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right A haddr)

/-
Witness-to-edge address alignment.

Checkpoint 220 asks whether a witness-derived interval pulse can supply the
Beam addressed target required by the exact-edge API above.  The answer is
asymmetric for the existing witness carrier:

* `SourcePressureLocalIslandWitness` stores the island center `W.val`;
* `sourcePressureIntervalPulseAddress_of_localIslandWitness W` is a singleton
  pulse with `start = W.val` and `len = 1`;
* hence the right edge `start + len - 1` is exactly `W.val`;
* the left edge `start - 1` is the depth before the island and is nonpositive
  by the interval-pulse crossing data, so it cannot be a Beam depth target.

Thus the current witness/list relation aligns with the interval-pulse right
edge, not with the left edge.  This is an exact-edge fact, not transport.
-/

/--
An explicit local-island witness contained in `L` supplies a Beam addressed
target at its own center depth.

This is the reusable center-depth alignment theorem.  It uses only membership
of the supplied witness in the supplied list; it does not claim list coverage.
-/
theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamAddressedDepthTarget L W.val := by
  have hcontains : SourcePressureBeamSeedContainsDepth L W.val :=
    ⟨W, hmem, rfl⟩
  exact
    sourcePressureBeamAddressedDepthTarget_mk hcontains
      (sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains)

/--
The singleton interval-pulse address generated by a local-island witness starts
at the witness center.

This is a pure coordinate projection.  It exists so Beam-facing pulse
diagnostics can be rewritten from interval-pulse coordinates back to the native
witness depth `W.val` without rebuilding any edge or mass-balance proof.
-/
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val := by
  simp [sourcePressureIntervalPulseAddress_of_localIslandWitness,
    sourcePressureIntervalPulseAddress_of_localIsland]

/--
The singleton interval-pulse address generated by a local-island witness has
right edge equal to the witness center.
-/
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 =
      W.val := by
  simp [sourcePressureIntervalPulseAddress_of_localIslandWitness,
    sourcePressureIntervalPulseAddress_of_localIsland]

/--
A local-island witness contained in `L` supplies the Beam addressed target at
the right edge of its generated singleton interval pulse.

This is the positive address-alignment result of cp220.
-/
theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamAddressedDepthTarget L
      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
  rw [sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq W]
  exact sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem hmem

/--
Witness-derived singleton pulses feed the False/Boundary Beam comparison at
their aligned right edge.

The edge alignment is not assumed externally: it is supplied by membership of
the witness in the explicit list `L`.
-/
theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamMassBalanceRightInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
      SourcePressureBeamMassBalanceLeftInt n k r
        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) :=
  sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
    (sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem)

/--
Witness-derived singleton pulses supply next-margin nonpositivity at their
aligned right edge.
-/
theorem sourcePressureMargin_next_nonpos_of_localIslandWitness_intervalPulse_right
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureMarginInt n k
        (r +
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) +
          1) ≤ 0 :=
  sourcePressureMargin_next_nonpos_of_intervalPulse_right
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
    (sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right hmem)

/--
The left edge of an interval-pulse address cannot be a Beam addressed target.

This is the negative side of the address-alignment investigation.  A Beam
addressed target implies positive margin at the addressed depth, while the
interval-pulse left crossing records that the left edge is nonpositive.
-/
theorem not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (A : SourcePressureIntervalPulseAddress n k r) :
    ¬ SourcePressureBeamAddressedDepthTarget L (A.start - 1) := by
  intro haddr
  have hpos := sourcePressureMargin_pos_of_addressedDepthTarget haddr
  have hnonpos := sourcePressureIntervalPulseAddress_before_start_nonpos A
  omega

/--
In particular, a witness-derived singleton interval pulse cannot supply a Beam
addressed target at its left edge.
-/
theorem not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (W : SourcePressureLocalIslandWitness n k r) :
    ¬ SourcePressureBeamAddressedDepthTarget L
      ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) :=
  not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)


end DkMath.Collatz
