# Collatz Finite Channel-Flow Layer

## Checkpoint 100 Summary

Checkpoint 100 closes the first finite channel-flow layer for the accelerated
Collatz map.

The theorem chain is:

```text
1. residue arithmetic
2. orbit-label transition
3. source distribution conservation
4. shifted-tail distribution conservation
5. pointwise-to-count channel-flow helper
6. recursive two-adic Petal instances
```

The important point is that this layer is entirely finite and natural-valued.

It does not use:

```text
limits
probability
real-valued density
asymptotic frequency
```

This is intentional.  The project first fixes exact finite conservation laws
before introducing any ratio or analytic language.

## Source And Tail Windows

For a starting odd state `n` and window size `k`, the source window is:

```text
i = 0, 1, ..., k - 1
```

with labels:

```lean
oddOrbitLabel n i
```

The shifted-tail window is:

```text
i + 1 = 1, 2, ..., k
```

It is counted by the same index range `i < k`, but each label is shifted one
step forward.

## Power-Of-Two Residue Cells

At depth `depth`, the residue modulus is:

```text
2^depth
```

The source count is:

```lean
orbitWindowResidueCountPow2 n k depth residue
```

and the tail count is:

```lean
orbitWindowResidueCountPow2Tail n k depth residue
```

These count how many source or shifted-tail labels occupy the chosen residue
cell.

## Conservation

At a fixed depth, every label belongs to exactly one residue cell.

The source conservation theorem is exposed as:

```lean
sourcePow2Distribution_total
```

It states:

```text
sum_{residue < 2^depth}
  sourceCount(depth, residue)
    = k
```

The shifted-tail conservation theorem is:

```lean
tailPow2Distribution_total
```

It states:

```text
sum_{residue < 2^depth}
  tailCount(depth, residue)
    = k
```

Thus source and tail are both finite distributions of total mass `k`.

## Channel Flow

The central abstraction is:

```lean
pow2ChannelFlow_of_pointwise
```

Informally:

```text
If every source label in cell A lands in shifted-tail cell B,
then occupation(A) <= occupation(B).
```

The exact shape is:

```text
pointwise theorem:
  for every i < k,
  source residue condition at i
    -> tail residue condition at i + 1

count theorem:
  source count <= tail count
```

This is the finite channel-flow bridge.

## Recursive Two-Adic Petal Instances

The recursive Petal residue channels now use the helper route.

Recovery channel:

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
```

Continuation channel:

```lean
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
```

These are thin wrappers around:

```lean
pow2ChannelFlow_of_pointwise
```

with pointwise inputs:

```lean
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

The message is:

```text
recursive residue arithmetic
  -> pointwise orbit transition
  -> count-level channel-flow inequality
```

## Why This Matters

Before this layer, the project could prove individual pointwise residue
transitions and some hand-written count inequalities.

After this layer, future channel statements should use the pattern:

```text
prove pointwise source-to-tail transition
apply channel-flow helper
obtain count inequality
```

This reduces duplication and makes the mathematical structure easier to read.

## Ratio Layer Is Next, But Not Yet Analytic

The natural next question is:

```text
what fraction of the window occupies a given channel?
```

However, the first ratio layer should stay in `Nat` inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

This gives a finite ratio witness without division.

Reasons:

```text
no zero-window division problem
no coercion overhead
no unnecessary real-analysis import pressure
```

Only after repeated use should the project introduce `ℚ` or `ℝ` frequency
definitions.

## Later Odd Factor Carrier Layer

The channel-flow layer is still purely 2-adic.

The later odd factor carrier layer would ask:

```text
inside a fixed two-adic residue cell,
which odd prime factors appear after the next transition?
```

That belongs to the next chapter.

The current checkpoint deliberately stops before that layer, so that the
finite 2-adic channel framework remains clean.
