# report-petal-239

## Checkpoint

`petal-239`

## Summary

Implemented Branch C.

I inspected the current pressure files for a direct neighbor/transport relation
from:

```lean
SourcePressureBeamCenteredLocalPulseBox n k r L W
```

to a neighboring witness or transport candidate.  The existing code has strong
adjacent-pair and obstruction machinery, but it is list/pair based:

```text
SourcePressureLocalIslandWitnessAdjacentPairInList
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
SourcePressureFailureResolution
```

There is not yet a direct relation of the form:

```text
boxed local pulse at W
  -> neighboring candidate W'
```

or:

```text
boxed local pulse at W
  -> transport obstruction
```

So this checkpoint adds only a small projection lemma for the most immediately
useful part of the cp238 box.

## Added Theorem

```lean
theorem SourcePressureBeamCenteredLocalPulseBox.signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureBeamCenteredLocalPulseBox n k r L W) :
    W ∈ L ∧
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

This theorem is local and witness-relative.  It simply projects the sign and
target part of the cp238 local pulse box.  It does not infer a neighboring
witness, transport, propagation, or obstruction.

## Search Result

Files inspected:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
DkMath/Collatz/PetalBridge/PressureAutomaton.lean
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
DkMath/Collatz/PetalBridge/PressureDecay.lean
DkMath/Collatz/PetalBridge/PressureFrontier.lean
DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

Useful existing surfaces:

```lean
SourcePressureFailureResolution
sourcePressureFailureResolution_of_sortedBeforeFailure
sourcePressureFailureResolution_recovered_of_noAdjacentOverlap

SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

These are about explicit list failure, adjacent pairs, recovered diagnostics,
and overlap obstruction.  They do not currently consume a single boxed pulse
witness and produce a neighbor.

## Missing Relation

The exact missing propagation relation is one of the following:

```text
SourcePressureBeamCenteredLocalPulseBox n k r L W
  -> ∃ W', NeighborCandidate L W W'
```

or:

```text
SourcePressureBeamCenteredLocalPulseBox n k r L W
  -> TransportObstruction L W ∨ ∃ W', NeighborCandidate L W W'
```

There is also a possible list-mediated version:

```text
SourcePressureBeamCenteredLocalPulseBox n k r L W
  -> SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
  -> SourcePressureFailureResolution L
```

but that requires an explicit list-level failure hypothesis.  The box alone
does not provide list failure.

## How cp238 Should Be Consumed

The cp238 box is best treated as a local diagnostic carrier:

```text
boxed pulse
  -> sign/target facts
  -> height/jump facts
  -> future neighbor or obstruction theorem
```

This checkpoint added the first projection:

```text
boxed pulse -> sign/target facts
```

The quantitative height/jump projection can be added next if caller noise
appears around the boxed bounds.

## Big / Core / Beam / Gap Classification

- Core:
  cp238 local pulse box remains the primary carrier.

- True Beam:
  the sign/target projection is now a named theorem, so callers can use the
  active pulse shape without unpacking all height and jump bounds.

- Boundary:
  the theorem only exposes facts already present in the box for one witness
  `W ∈ L`.

- False Beam:
  no transport, neighbor selection, propagation, or obstruction follows from
  the box alone.

- Gap:
  the missing object is a real neighbor-candidate or transport-obstruction
  relation connecting one boxed pulse to adjacent witness/list structure.

## Next Branch Prediction

The next useful branch is to introduce a thin local relation only if it matches
existing list machinery.  Candidate names:

```text
SourcePressureBeamNeighborCandidate
SourcePressureBeamPulseTransportObstruction
SourcePressureBeamPulseTransportResolution
```

The safest next step is not to assert propagation, but to define or discover a
small relation that says what it means for a boxed pulse to have a neighboring
candidate.  Once that relation exists, the current adjacent-pair and overlap
obstruction API can be connected without overstating global behavior.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" <pressure-file-scope>
git diff --check
```

Results:

```text
PressureDecay build: pass
PressureBeam.Pulse build: pass
PressureBeam build: pass
PetalBridge build: pass
no-sorry grep: no matches in inspected pressure scope
git diff --check: pass
```
