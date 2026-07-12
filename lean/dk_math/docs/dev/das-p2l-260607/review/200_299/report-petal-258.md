# Report: petal-258

## Goal

Add small caller-facing consequences of:

```lean
SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
```

The target is the non-collision / reverse-order-exclusion surface:

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> W.val != W'.val
  -> not W'.val <= W.val
```

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
```

Both are direct wrappers over `val_lt_of_sorted`.

## Meaning

Downstream callers no longer need to destruct or re-prove the strict order
when they only need one of the following lighter facts:

```lean
W.val != W'.val
not W'.val <= W.val
```

This keeps later non-collision and reverse-orientation branches short and
stable.

## Guardrails

These theorems do not add a new mathematical invariant.  They are API wrappers
around the sorted oriented neighbor box comparison:

```lean
hbox.val_lt_of_sorted hsorted
```

They remain local to the explicit two-endpoint box and the supplied sortedness
invariant.  They do not imply global uniqueness of pressure depths, global
coverage, transport, propagation, or convergence.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate for this checkpoint.

## Next Branch Prediction

The next useful layer is pair comparison proper.

Candidate branch:

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> reverse order impossible
  -> pair-comparison branch can select the forward orientation
```

If a caller needs address-level negation rather than value-level negation, add
the corresponding wrapper at the address-before layer.  Otherwise,
`not_val_ge_of_sorted` should be enough for the next local comparison branch.
