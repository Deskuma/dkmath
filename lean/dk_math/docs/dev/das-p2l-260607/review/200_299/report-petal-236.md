# report-petal-236

## Checkpoint

`petal-236`

## Result

Implemented Branch A.

The first finite local Big box for source pressure margins is now available at
the generic `PressureDecay` layer.

## Added Theorems

```lean
theorem sourcePressureMarginInt_le_two_mul_window
    (n : OddNat) (k r : ℕ) :
    SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
```

```lean
theorem neg_window_le_sourcePressureMarginInt
    (n : OddNat) (k r : ℕ) :
    - (k : ℤ) ≤ SourcePressureMarginInt n k r
```

```lean
theorem sourcePressureMarginInt_bounds_window
    (n : OddNat) (k r : ℕ) :
    - (k : ℤ) ≤ SourcePressureMarginInt n k r ∧
      SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
```

## Meaning

By definition:

```text
SourcePressureMarginInt n k r
  = 2 * continuation - retention
```

The existing finite window bounds provide:

```text
continuation ≤ k
retention ≤ k
```

Therefore every pointwise source-pressure margin lies in:

```text
[-k, 2k]
```

This is a finite local Big bound.  It is not propagation, not list coverage,
not aggregation of witness families, and not a global Collatz statement.

## Branch D Decision

No seed-specific wrapper was added in this checkpoint.

The generic bounds are cleaner and apply to every pressure depth.  A future
wrapper can combine:

```lean
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
sourcePressureMarginInt_bounds_window
```

to say that the three centered pulse margins all live inside the finite local
box `[-k, 2k]`.  That wrapper should be added only if a caller needs the bundled
surface.

## Beam Classification

- True Beam: positive pulse height is now bounded above by `2k`.
- Boundary / False Beam: nonpositive margins are still bounded below by `-k`.
- Core: the margin-height box is generic and independent of witness selection.
- Gap: no net-drop bound, local Big upper estimate, propagation, or convergence
  has been claimed yet.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` or `admit` was found in the requested pressure-file grep scope.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Branch

The next natural branch is either:

1. Bundle cp235 sign transition with the new `[-k, 2k]` margin bounds for the
   three involved depths.
2. Inspect `SourcePressureNetDropInt`, `SourceRetentionDropInt`, and
   `SourceContinuationDropInt` for analogous finite local bounds.

The second branch is likely more foundational: net-drop bounds would turn
local pulse transitions into bounded finite jumps, not just bounded pointwise
heights.
