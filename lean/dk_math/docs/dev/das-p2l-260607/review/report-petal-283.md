# Report: petal-283

## Goal

Move beyond corridor API cleanup and use the existing FPC corridor surfaces to
build a local positive-pulse packing obstruction.

The work deliberately treats this as a local phenomenon.  It does not attempt
to prove or discuss the global Collatz conjecture.

## Implemented

Added FPC-level consumer theorems:

- `SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers`
- `SourcePressureForwardPairComparisonState.two_le_value_gap`
- `SourcePressureForwardPairComparisonState.two_le_index_gap`

Added upstream lifted split theorems:

- `sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap`
- `sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap`
- `sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap`

## Established Facts

For any
`h : SourcePressureForwardPairComparisonState L W W'`, Lean now proves that
there exists an index `m` strictly between the two positive center indices:

```lean
∃ m : ℕ,
  r + W.val < m ∧
    m < r + W'.val ∧
      SourcePressureMarginInt n k m <= 0
```

The witness is the left next boundary:

```lean
m = r + W.val + 1
```

Lean also proves the compact spacing facts:

```lean
W.val + 2 <= W'.val
r + W.val + 2 <= r + W'.val
```

## Upstream Route

The state ladder now exposes the local packing obstruction directly:

```text
FailureResolution + sorted(L)
  -> nonpositive separator between two positive centers
   ∨ concrete adjacent-pair overlap obstruction

SortedFailure + sorted(L)
  -> nonpositive separator between two positive centers
   ∨ concrete adjacent-pair overlap obstruction

BeamSeed + sorted(L)
  -> nonpositive separator between two positive centers
   ∨ concrete adjacent-pair overlap obstruction
```

This is the first local Big / packing-bound style surface in the current
PressureState branch: forward positive centers cannot be packed consecutively
without a nonpositive separator between them.

## What Can Be Concluded

Within a sorted explicit witness list, the BeamSeed/FailureResolution route has
two possible local outcomes:

1. the forward pair branch yields two positive centers with a certified
   nonpositive separator strictly between them;
2. the obstruction branch yields a concrete adjacent-pair overlap obstruction.

This is a local structural fact about explicit witnesses and margins.

## Guardrails

This checkpoint does not prove:

- global positive-center uniqueness;
- arbitrary window disjointness;
- all interior corridor indices are nonpositive;
- global coverage of all possible centers;
- any global Collatz termination statement.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
```

Final gate:

```text
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The next natural local phenomenon to isolate is a named packing state:

```text
SourcePressureLocalPackingSeparatorState L W W' m
```

This should be added only if repeated callers need to carry the separator
package.  Otherwise, the current upstream split theorems are already a usable
surface for local packing-bound experiments.
