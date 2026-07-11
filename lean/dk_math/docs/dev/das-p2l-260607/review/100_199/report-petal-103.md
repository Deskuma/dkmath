# Report Petal 103

## Summary

Checkpoint 103 completed the shifted-tail counterpart of the depth refinement
introduced in checkpoint 102.

The source window and shifted-tail window now both support the same recursive
Petal split:

```text
retention = recovery + continuation
```

## Implemented Lean Surface

Tail count refinement:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
```

Tail retention split:

```lean
orbitWindowRetentionMassPow2Tail_split
```

Tail child bounds:

```lean
orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
```

Forcing aliases:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

## Mathematical Reading

Checkpoint 102 gave:

```text
M_r = R_r + K_r
```

for source-window retention mass.

Checkpoint 103 gives:

```text
M_tail_r = R_tail_r + K_tail_r
```

for shifted-tail retention mass.

Together with the existing channel-flow theorem, the continuation channel now
has a clean finite mass-flow reading:

```text
source continuation mass
  <= shifted-tail retention mass
  = shifted-tail recovery mass + shifted-tail continuation mass
```

This does not prove contraction.  It fixes the destination budget of the
continuation mass inside the next observation window.

## Docs Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md
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

## Extra Result

The initially proposed next-step theorem was small enough to implement in this
checkpoint:

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

It packages:

```text
source continuation <= tail retention
tail retention = tail recovery + tail continuation
```

into:

```text
source continuation <= tail recovery + tail continuation
```

## Next Inference

The next checkpoint can now focus on a genuine contraction or obstruction
condition rather than the bookkeeping chain.

Candidate shapes:

```lean
AtMostHalf
  (orbitWindowContinuationSiblingMassPow2 n k (r + 1))
  (orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
    orbitWindowContinuationSiblingMassPow2Tail n k (r + 1))
```

or a contradiction-style theorem showing that a proposed low-peeling cylinder
cannot be closed under too many consecutive continuation steps without
exceeding the finite window budget.
