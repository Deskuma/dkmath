# Report Petal 102

## Summary

Checkpoint 102 implemented the depth-refinement split for power-of-two residue
cells in `DkMath.Collatz.PetalBridge`.

The main result is now verified:

```lean
orbitWindowRetentionMass_split
```

which states that retention mass at depth `r` is exactly the sum of the
recovery and continuation sibling masses at depth `r + 1`.

## Implemented Lean Surface

New window bounds:

```lean
orbitWindowRecoverySiblingMassPow2Tail_le_window
orbitWindowContinuationSiblingMassPow2Tail_le_window
```

Residue validity:

```lean
twoAdicRetentionResidue_lt_pow
```

Pointwise refinement:

```lean
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
```

Indicator and count refinement:

```lean
pow2ResidueIndicator_refine_succ
orbitWindowResidueCountPow2_refine_succ
```

Retention split and child bounds:

```lean
orbitWindowRetentionMass_split
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
```

## Mathematical Reading

For a valid cell modulo `2^depth`, the next modulus `2^(depth+1)` has exactly
two child cells:

```text
residue
residue + 2^depth
```

The finite source-window count of the parent cell is therefore the sum of the
two child counts.

Specialized to the retention residue `2^r - 1`, this becomes:

```text
retention_r = recovery_r + continuation_r
```

This closes the first recursive Petal decomposition for Collatz residue mass.

## Docs Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md
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

The next useful theorem should use `orbitWindowRetentionMass_split` as the
starting point, not raw residue-count unfolding.

Two natural directions:

```text
1. contraction / ratio:
   show continuation is at most half of retention under a suitable condition

2. forcing / flow:
   large continuation mass forces large shifted-tail retention mass through
   the existing channel-flow theorems
```

The second direction is probably easier because the file already contains
channel-flow inequalities such as:

```lean
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
```

Suggested next checkpoint:

```lean
theorem orbitWindowContinuationMass_forces_tailRetention
```

with the exact statement chosen by matching existing mass names rather than
creating another raw residue-count theorem.
