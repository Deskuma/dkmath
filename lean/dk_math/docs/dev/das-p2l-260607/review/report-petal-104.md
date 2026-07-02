# Report Petal 104

## Summary

Checkpoint 104 added the finite half-criterion layer for Collatz Petal mass
splits.

The new results do not prove contraction.  They prove conditional arithmetic
bridges:

```text
continuation <= recovery
  -> continuation is at most half of retention
```

for both source and shifted-tail windows.

## Implemented Lean Surface

Source half criterion:

```lean
atMostHalf_continuation_of_continuation_le_recovery
```

Tail half criterion:

```lean
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

Recovery-budget variants:

```lean
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

Ratio witness bridges:

```lean
continuation_atMostRatio_one_one_retention
tailContinuation_atMostRatio_one_one_retention
recovery_atMostRatio_one_one_retention
tailRecovery_atMostRatio_one_one_retention
```

Tail-budget alias:

```lean
orbitWindowContinuationMass_tailBudget
```

## Mathematical Reading

With the split:

```text
M = R + K
```

if:

```text
K <= R
```

then:

```text
2K <= M
```

This is the exact finite arithmetic bridge from recovery/continuation
comparison to a half-mass statement.

## Docs Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.

Known upstream warning remains unchanged:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Inference

The bookkeeping layer is now clear:

```text
split exists
comparison condition exists
AtMostHalf follows
```

The next mathematical target is the missing comparison condition itself.

Candidate directions:

```text
1. height drift:
   show continuation-heavy paths force later extra peeling

2. obstruction:
   show persistent continuation creates an impossible address/collision pattern

3. carrier information:
   use odd-factor or Petal carrier structure to force recovery mass
```

The most Lean-friendly next checkpoint is probably a conditional obstruction
lemma: assume continuation stays larger than recovery across a finite range of
depths, then record the exact accumulated tail-budget pressure it creates.
