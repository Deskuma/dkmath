# Report Petal 098: Tail Partition and Channel-Flow Helper

## Checkpoint

This checkpoint follows `__next_implementation-098.md`.

The main target was the shifted-tail analogue of the generic power-of-two
residue partition:

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
```

The requested extra direction was the reusable pointwise-to-count bridge:

```lean
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
```

Both targets are now implemented without adding `sorry`.

## Implemented Lean Surface

Added in `DkMath.Collatz.PetalBridge`:

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : Nat) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k

theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : Nat)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

The tail partition uses the same proof pattern as the source partition:

```text
tail successor formula
single-label residue indicator sum
induction on k
```

The generic helper abstracts the repeated proof shape:

```text
pointwise residue transition
  -> count-level source <= shifted-tail target
```

## Mathematical Reading

The bridge now has both finite distribution laws:

```text
source window:
  Sum_{residue < 2^depth} CountPow2(depth, residue) = k

shifted tail window:
  Sum_{residue < 2^depth} TailCountPow2(depth, residue) = k
```

So the observation can be read as a finite channel-flow system:

```text
source residue distribution
  -> pointwise transition law
  -> tail residue distribution
```

This is still purely natural-valued.  No rational or real frequency layer is
introduced yet.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status document now records:

```text
full pow-two shifted-tail residue partition
generic pointwise-to-count channel flow
```

## Inference

The helper is the important new reusable API.

Previously, each count-level transition had to be proved by its own induction.
Now the intended route is:

```text
prove a pointwise theorem:
  if label i is in source cell A,
  then label i+1 is in tail cell B

apply:
  orbitWindowResidueCountPow2_le_tail_of_pointwise

obtain:
  Count(source A) <= TailCount(target B)
```

This should allow future recovery / continuation / retention channel theorems
to be stated as thin corollaries of pointwise residue lemmas.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

Known upstream warning remains unchanged:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new `sorry` was added to `DkMath.Collatz.PetalBridge`.

## Next Implementation Candidates

The next practical step is to re-express existing count transition theorems via
the generic helper:

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
```

These can become short applications of:

```lean
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

with pointwise inputs:

```lean
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

After that refactor, similar future channel-flow lemmas should only need a
pointwise transition theorem plus one helper application.
