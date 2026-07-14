# report-petal-234

## Checkpoint

`petal-234`

## Result

Implemented Branch B + Branch A + Branch C in the requested three-theorem
limit.

The checkpoint target was the coordinate mismatch between:

- Core depth-target vocabulary at native witness depth `W.val`;
- Pulse singleton diagnostics stated in interval-pulse coordinates.

For a witness-generated singleton pulse, the interval address has
`start = W.val` and right edge `start + len - 1 = W.val`.  The right-edge
alignment already existed, so this checkpoint only added the missing `start`
projection and then exposed centered Pulse diagnostics.

## Added Theorems

### Branch B: coordinate helper

```lean
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val
```

This is a pure coordinate projection.  It does not mention Beam diagnostics,
coverage, propagation, or global Collatz behavior.

### Branch A: witness centered diagnostic

```lean
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (hmem : W ∈ L) :
    SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
      SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
      SourcePressureBeamAddressedDepthTarget L W.val ∧
        SourcePressureBeamMassBalanceRightInt n k r W.val ≤
          SourcePressureBeamMassBalanceLeftInt n k r W.val
```

This consumes the existing interval-coordinate full diagnostic and rewrites:

- entry edge by `sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq`;
- center/right edge by `sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq`.

No low-level edge proof was rebuilt.

### Branch C: seed centered diagnostic

```lean
theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W.val
```

This combines seed witness extraction with the centered singleton diagnostic.
The witness remains existential.  No canonical witness, coverage, aggregation,
overlap repair, propagation, or convergence is claimed.

## Beam Classification

- True Beam: the entry edge `W.val - 1` has `left < right`.
- Boundary / False Beam: the center/right edge `W.val` has `right <= left`.
- Core: `SourcePressureBeamAddressedDepthTarget L W.val` is now visible in the
  same centered theorem as the Beam comparisons.
- Gap: no list-wide coverage or propagation theorem is added.  This checkpoint
  only fixes local coordinate readability.

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

The next useful branch is to decide whether centered versions are needed for
existing adjacent-pair / overlap wrappers.

Do not add them automatically unless caller noise appears.  The current
centered seed theorem is the clean public surface for seed-level use.  If a
future caller remains at the adjacent-overlap layer and repeatedly rewrites
interval coordinates, add a pair-preserving centered wrapper for that caller
only.
