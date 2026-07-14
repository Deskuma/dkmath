# Report: petal-242

## Branch

Continued from the petal-241 next-branch prediction.

Taken branch:

- Beam-facing oriented adjacent-pair diagnostics.

The implementation stays in `PressureBeam/Pulse.lean` because the new theorems
are Beam-facing wrappers over existing lower adjacent-diagnosis carriers.

## Implemented Theorems

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

Added:

```lean
theorem sourcePressureBeamNeighborCandidate_forward_center_full_diagnostics_of_adjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W') :
    SourcePressureBeamNeighborCandidate L W W' ∧
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' ∧
        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
                SourcePressureBeamAddressedDepthTarget L W'.val ∧
                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
                    SourcePressureBeamMassBalanceLeftInt n k r W'.val
```

```lean
theorem sourcePressureBeamNeighborCandidate_reverse_center_full_diagnostics_of_adjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W' W)
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W) :
    SourcePressureBeamNeighborCandidate L W W' ∧
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W' W ∧
        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W.val ∧
              SourcePressureBeamMassBalanceLeftInt n k r (W'.val - 1) <
                SourcePressureBeamMassBalanceRightInt n k r (W'.val - 1) ∧
                SourcePressureBeamAddressedDepthTarget L W'.val ∧
                  SourcePressureBeamMassBalanceRightInt n k r W'.val ≤
                    SourcePressureBeamMassBalanceLeftInt n k r W'.val
```

## Meaning

The cp241 theorem gave:

```text
SourcePressureBeamNeighborCandidate L W W'
  -> W' centered singleton diagnostic
```

This checkpoint adds the orientation-aware version:

```text
AdjacentPairInList L W W'
  + AdjacentDiagnosis L W W'
  -> Beam neighbor candidate
  -> centered diagnostics for both W and W'
  -> same oriented adjacent diagnosis is preserved
```

and the reverse case:

```text
AdjacentPairInList L W' W
  + AdjacentDiagnosis L W' W
  -> Beam neighbor candidate for W,W'
  -> centered diagnostics for both W and W'
  -> same reverse-oriented adjacent diagnosis is preserved
```

The point is that the symmetric Beam candidate is not used to guess an
orientation.  The caller supplies the orientation by giving the ordered
adjacent-pair address and the ordered adjacent diagnosis.

## Classification

Core:

- The explicit ordered adjacent-pair evidence is retained.
- The existing adjacent diagnosis is retained in its original orientation.

True Beam:

- Both endpoints expose their centered entry comparison at `val - 1`.

Boundary:

- The orientation is an input boundary condition.
- The symmetric `SourcePressureBeamNeighborCandidate` is only reconstructed
  from the supplied orientation.

False Beam:

- Both endpoints expose their centered exit comparison at `val`.

Gap:

- The theorem still does not classify the ordered diagnosis branch as recovered
  or overlap.
- It does not repair overlap, transport diagnostics, aggregate witnesses,
  choose a canonical pair, prove coverage, or imply Collatz convergence.

## Next Branch Prediction

The next useful branch is probably a small elimination wrapper:

```text
Beam oriented neighbor diagnostic
  -> recovered branch evidence
   ∨ overlap obstruction evidence
```

However, this should be added only if a caller starts destructing
`SourcePressureLocalIslandWitnessAdjacentDiagnosis` repeatedly.  For now, the
current surface is deliberately conservative: it preserves the ordered
diagnosis carrier without opening it.

The automaton/failure-resolution branch remains useful later:

```text
SourcePressureFailureResolution L
  -> exists ordered adjacent pair A B
  -> Beam-facing oriented adjacent diagnostic surface
```

That branch should wait until a caller actually wants to enter from
`SourcePressureFailureResolution`.

## Verification

Commands run from:

```text
lean/dk_math
```

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

No-sorry check over inspected pressure files:

```text
rg -n "sorry|admit" \
  PressureBeam/Pulse.lean \
  PressureBeam/Core.lean \
  PressureAdjacentDiagnosis.lean \
  PressureLocalWitnessObstruction.lean \
  PressureDiagnosticDecomposition.lean \
  PressureAutomaton.lean
```

Result: no matches.

Whitespace check:

```text
git diff --check
```

Result: passed.
