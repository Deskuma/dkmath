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

end DkMath.Collatz
