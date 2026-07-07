# Report: petal-259

## Goal

Exclude reverse box orientation under the same sorted witness list.

Target theorem:

```lean
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
```

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
```

The proof is the expected local contradiction:

```text
forward box + sorted(L) -> W.val < W'.val
reverse box + sorted(L) -> W'.val <= W.val
```

These two facts are incompatible.

## Meaning

The oriented two-endpoint box now has an explicit anti-symmetry-style surface:

```text
SourcePressureOrientedNeighborBoxState L W W'
  + SourcePressureLocalIslandWitnessListSortedBefore L
  -> not SourcePressureOrientedNeighborBoxState L W' W
```

This is the first direct reverse-orientation exclusion theorem at the box
layer.

## Guardrails

This theorem is still local to:

* the explicit forward box;
* the proposed reverse box;
* the same sorted witness list.

It does not choose a canonical box, does not sort an arbitrary list, does not
claim all pairs are represented, and does not add any global Collatz claim.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

`git diff --check` is run as the final whitespace gate.

## Next Branch Prediction

The next layer can use the split:

```text
Box(W,W') or PairOverlap
```

On the `Box` side, sortedness now fixes the forward orientation and rules out
the reverse box.  On the `PairOverlap` side, the obstruction remains separate.

The natural next theorem shape is:

```text
sorted(L)
  + (oriented box or pair overlap)
  -> (forward-oriented value comparison and not reverse box) or pair overlap
```

This would prepare the pair-comparison layer without merging the obstruction
branch into the diagnostic branch.
