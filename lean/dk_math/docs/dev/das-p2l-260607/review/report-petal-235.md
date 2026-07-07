# report-petal-235

## Checkpoint

`petal-235`

## Result

Implemented Branch A.

The centered seed diagnostic from cp234 now feeds a centered local
margin-sign transition theorem.

## Added Theorem

```lean
theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

## Margin Index Convention

The discovered convention is:

```text
mass-balance at edge j
  classifies the next margin at r + j + 1
```

Therefore:

```text
entry edge  = W.val - 1
entry sign  = positivity at r + (W.val - 1) + 1 = r + W.val

exit edge   = W.val
exit sign   = nonpositivity at r + W.val + 1
```

The previous sign at `r + (W.val - 1)` is obtained from the local-island
witness itself.

## Proof Chain

The theorem consumes:

```lean
exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
```

which supplies:

```text
W ∈ L
MassBalanceLeft (W.val - 1) < MassBalanceRight (W.val - 1)
SourcePressureBeamAddressedDepthTarget L W.val
MassBalanceRight W.val ≤ MassBalanceLeft W.val
```

Then:

```lean
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
```

converts the entry comparison to positive margin at `r + W.val`, and:

```lean
sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
```

converts the exit comparison to nonpositive margin at `r + W.val + 1`.

## Beam Classification

- True Beam: `0 < SourcePressureMarginInt n k (r + W.val)`.
- Boundary / False Beam:
  `SourcePressureMarginInt n k (r + W.val + 1) ≤ 0`.
- Core: `SourcePressureBeamAddressedDepthTarget L W.val` remains visible.
- Gap: no propagation, coverage, local Big bound, or convergence is claimed.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
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

The next branch can attack local Big bounds, but only if an existing theorem
already turns this sign pattern into a bounded local estimate without adding
propagation or list coverage.

Recommended next search:

```text
SourcePressureMarginInt
SourcePressureNetDropInt
retention mass
continuation mass
local Big / upper bound
```

If no direct bridge exists, add a report-only chain first and postpone the
theorem.
