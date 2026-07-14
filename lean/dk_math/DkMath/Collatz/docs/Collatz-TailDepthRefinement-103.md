# Collatz Tail Depth Refinement 103

Checkpoint 103 closes the shifted-tail side of the recursive Petal split.

Checkpoint 102 proved the source-window split:

```lean
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
```

Checkpoint 103 adds the matching shifted-tail split:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
```

## Tail Count Split

The general theorem is:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
```

It says that shifted-tail occupation in a valid parent residue cell at depth
`depth` is the sum of occupation in its two child cells at depth `depth + 1`.

In formula form:

```text
tailCount(depth, residue)
  =
tailCount(depth+1, residue)
  + tailCount(depth+1, residue + 2^depth)
```

The proof uses the same pointwise indicator theorem as the source case:

```lean
pow2ResidueIndicator_refine_succ
```

The only difference is that the point being counted is
`oddOrbitLabel n (i + 1)`.

## Tail Retention Split

The named tail retention theorem is:

```lean
orbitWindowRetentionMassPow2Tail_split
```

It reads:

```text
tail retention mass at depth r
  =
tail recovery sibling mass at depth r+1
  + tail continuation sibling mass at depth r+1
```

This gives source/tail symmetry:

```text
M_r        = R_r        + K_r
M_tail_r   = R_tail_r   + K_tail_r
```

## Child Bounds

The child masses are bounded by their parent tail retention mass:

```lean
orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
```

These are direct consequences of the tail split.

## Forcing Aliases

Two aliases were added to make later mass-flow arguments read naturally:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

They restate existing recursive channel-flow theorems with forcing-oriented
names.

The important chain is now:

```text
source continuation mass
  <= tail retention mass
  = tail recovery mass + tail continuation mass
```

This is the first clean finite mass-flow grammar for following a low-peeling
Collatz segment through nested Petal cylinders.

## Packaged Continuation Budget

The two-line chain is also packaged directly as:

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

This theorem combines:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRetentionMassPow2Tail_split
```

It does not prove contraction by itself, but it exposes the exact destination
budget of continuation mass.
