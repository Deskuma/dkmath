# report-petal-220

## Checkpoint

`petal-220`

## Goal

Investigate the remaining address-alignment gap between interval-pulse exact
edges and Beam addressed targets.

cp219 established:

```text
interval pulse
  -> exact edge sign-change
  -> Beam mass-balance comparison
```

provided that a Beam addressed target is supplied at the same edge.

This checkpoint asks whether witness-derived structures can supply that
addressed target.

## Structures inspected

### `SourcePressureLocalIslandWitness`

Defined in `PressureAccounting` as:

```lean
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : Nat) :=
  { j : Nat // SourcePressureLocalIsland n k r j }
```

The witness stores the local-island center depth:

```text
W.val
```

It does not store both pulse edges as separate addresses.

### `sourcePressureIntervalPulseAddress_of_localIslandWitness`

This converts a local-island witness into a singleton interval-pulse address:

```lean
sourcePressureIntervalPulseAddress_of_localIsland n k r W.val W.property
```

Therefore the generated pulse has:

```text
start = W.val
len   = 1
```

Its exact edges are:

```text
left edge  = W.val - 1
right edge = W.val + 1 - 1 = W.val
```

### `SourcePressureBeamAddressedDepthTarget`

This requires both:

```lean
SourcePressureBeamSeedContainsDepth L j
SourcePressureBeamDepthTarget n k r j
```

Containment is exact:

```lean
∃ W ∈ L, W.val = j
```

Thus a witness list naturally contains the center `W.val`, not the left edge
`W.val - 1`.

## Lean changes

File changed:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
```

Added a witness-to-edge alignment comment block and seven theorems:

```lean
theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right
theorem sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right
theorem sourcePressureMargin_next_nonpos_of_localIslandWitness_intervalPulse_right
theorem not_sourcePressureBeamAddressedDepthTarget_intervalPulse_left
theorem not_sourcePressureBeamAddressedDepthTarget_localIslandWitness_intervalPulse_left
```

## Main finding

The address alignment is asymmetric.

### Right edge: aligned

For a witness-derived singleton pulse:

```text
right edge = start + len - 1 = W.val
```

Since `W ∈ L` supplies exact containment at `W.val`, Lean can construct:

```lean
SourcePressureBeamAddressedDepthTarget L
  ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1)
```

This feeds the cp219 interval-pulse right-edge theorem and gives:

```lean
SourcePressureBeamMassBalanceRightInt n k r rightEdge ≤
  SourcePressureBeamMassBalanceLeftInt n k r rightEdge
```

and next-margin nonpositivity at the same right edge.

Classification: `False Beam / Boundary`, exact-edge bridge.

### Left edge: not aligned, and actually impossible as a Beam target

For an interval-pulse address:

```text
left edge = A.start - 1
```

The pulse left crossing records:

```lean
SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0
```

But a Beam addressed target implies:

```lean
0 < SourcePressureMarginInt n k (r + (A.start - 1))
```

So Lean proves:

```lean
¬ SourcePressureBeamAddressedDepthTarget L (A.start - 1)
```

This is stronger than a mere missing containment relation.  The left edge is
the nonpositive side of the crossing, so it cannot be a Beam depth target under
the current definition.

Classification: `False / obstruction`, exact-edge negative theorem.

## Boundary

No equality-specific upstream source was added.  The right-edge theorem gives
the non-strict false/boundary side because `SourcePressureSignChangeDown`
stores next-margin nonpositivity.

The equality boundary remains the existing mass-balance equality API.

## Gap

The previous “address alignment gap” is now sharpened:

```text
witness center aligns with singleton pulse right edge
left edge is not a Beam target at all
```

Therefore, a future True Beam route cannot use the interval-pulse left edge as
a Beam addressed target under the current target definition.  It must either:

1. use a separate crossing-edge carrier that does not require positive current
   margin, or
2. read True Beam at the next positive depth rather than at the left edge
   itself, or
3. introduce a new boundary/crossing target vocabulary distinct from
   `SourcePressureBeamDepthTarget`.

This is not a failure.  It clarifies that Beam depth targets are positive
depths, while left crossings live immediately before the positive run.

## Guardrails

The new theorems are exact-edge and witness-local.

They do not assert:

- arbitrary target transport;
- global interval coverage;
- aggregation over witness families;
- canonical target selection;
- overlap repair;
- Collatz convergence.

## Verification

Commands run:

```bash
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry grep over inspected files: no matches.
- `git diff --check`: passed.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next candidate

The next useful step is to name the left-edge crossing target separately.

Current target:

```lean
SourcePressureBeamDepthTarget n k r j
```

means positive current margin.

But the left edge of a pulse is a crossing boundary:

```lean
SourcePressureMarginInt n k (r + j) ≤ 0
0 < SourcePressureMarginInt n k (r + j + 1)
```

Candidate vocabulary:

```lean
def SourcePressureBeamCrossingEdgeTarget (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureSignChangeUp n k r j
```

This would let the True Beam side talk about crossing edges without falsely
requiring the left edge itself to be a positive depth target.
