/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

#print "file: DkMath.Collatz.PetalBridge.PressureAutomaton"

namespace DkMath.Collatz

/-
Checkpoint 199: upper-level pressure automaton surface.

This file is deliberately above `PressureDiagnosticDecomposition`.  It gives a
readable automaton-style name to the already proved local failure-resolution
surface:

```text
sorted-before failure
  -> recovered adjacent pair diagnostic
     or adjacent overlap obstruction
```

No new proof strength is introduced here.  In particular, this layer does not
enumerate diagnostics, choose a canonical first diagnosis, aggregate recovered
families, repair overlap, prove coverage, or prove Collatz convergence.
-/

/--
Automaton-style resolution state for an explicit local-island witness list
whose sorted-before order has failed.

The state has exactly two branches:

* some adjacent pair has the named pair-local recovered diagnostic;
* or an adjacent overlap obstruction is present.

This is only a name for the already proved diagnostic decomposition surface.
Overlap remains an obstruction branch.
-/
def SourcePressureFailureResolution
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  (∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
        A B) ∨
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

/--
Sorted-before failure enters the pressure failure-resolution automaton.

This theorem is a naming wrapper around
`sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`.
It does not add a new decomposition theorem; it only exposes the existing
branch split as a single automaton-style state.
-/
theorem sourcePressureFailureResolution_of_sortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureFailureResolution L :=
  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
    h

/--
If the overlap branch is excluded, sorted-before failure resolves to a
recovered adjacent pair diagnostic.

This is the automaton-facing name for
`sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`.
The no-overlap hypothesis is consumed here; without it, overlap remains a
separate obstruction branch.
-/
theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
          A B :=
  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
    h hno

end DkMath.Collatz
