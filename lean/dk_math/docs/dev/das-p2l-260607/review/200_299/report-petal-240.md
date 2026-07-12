# report-petal-240

## Checkpoint

`petal-240`

## Summary

Implemented Branch A plus the Branch C consumer surface.

The new neighbor surface is intentionally explicit-adjacency based.  It does
not infer a neighbor from a boxed local pulse.  The role split is:

```text
SourcePressureBeamCenteredLocalPulseBox
  carries local sign/height/jump diagnostics for W

SourcePressureBeamNeighborCandidate
  carries explicit list adjacency between W and W'
```

This keeps the cp239 guardrail intact:

```text
box alone does not create a neighbor
```

## Added Predicate

```lean
def SourcePressureBeamNeighborCandidate
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∨
    SourcePressureLocalIslandWitnessAdjacentPairInList L W' W
```

Meaning:

```text
W and W' are adjacent in the explicit witness list L,
in either order.
```

This is only a symmetric Beam-facing name for the existing list/pair adjacency
predicate.  It does not claim transport, propagation, coverage, sorting,
overlap repair, or convergence.

## Added Consumer Theorem

```lean
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
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

This theorem consumes:

```text
boxed local pulse for W
+ explicit neighbor candidate W'
```

and returns:

```text
the neighbor candidate unchanged
+ sign/target facts for W
```

It does not assert that `W'` has a pulse box, that `W'` is reachable by
transport, or that a neighbor exists from `hbox` alone.

## Branch Notes

I did not add separate left/right constructor lemmas in this checkpoint.
The predicate is an `Or`, so callers can construct it directly with:

```lean
Or.inl hAdjacentLeft
Or.inr hAdjacentRight
```

Keeping the first surface small leaves room for the next checkpoint to decide
whether named constructors are actually useful at call sites.

## Big / Core / Beam / Gap Classification

- Core:
  the existing `SourcePressureLocalIslandWitnessAdjacentPairInList` relation is
  now available through a Beam-facing symmetric name.

- True Beam:
  local pulse diagnostics can now be combined with an explicitly supplied
  neighbor candidate without unpacking unrelated box components.

- Boundary:
  the neighbor candidate is supplied by list structure.  It is not derived from
  the pulse box.

- False Beam:
  no propagation, no transport success, no neighbor existence from one boxed
  witness, and no statement about `W'`'s own diagnostics is proved.

- Gap:
  the next missing bridge is from neighbor candidates to adjacent-pair
  diagnostics or failure-resolution branches.

## Next Branch Prediction

The next useful branch should connect:

```text
SourcePressureBeamNeighborCandidate L W W'
```

to existing adjacent-pair machinery:

```text
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureFailureResolution
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
```

There are two plausible directions:

1. Add tiny left/right constructor aliases if caller code becomes noisy.
2. Prove a consumer theorem:

```text
neighbor candidate
+ adjacent diagnosis on the oriented pair
-> Beam-facing neighbor diagnostic surface
```

The second direction is more valuable if a concrete caller needs to combine
local pulse boxes with recovered/overlap adjacent-pair diagnostics.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" <inspected-pressure-file-scope>
git diff --check
```

Results:

```text
PressureBeam.Pulse build: pass
PressureBeam build: pass
PetalBridge build: pass
no-sorry grep: no matches in inspected pressure scope
git diff --check: pass
```
