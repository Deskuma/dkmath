# Report Petal 099: Helper-Routed Recursive Channel Flow

## Checkpoint

This checkpoint follows `__next_implementation-099.md`.

The main goal was to connect the existing recursive two-adic Petal count
theorems to the generic pointwise-to-count helper introduced in checkpoint 098.

The checkpoint also requested depth-`3` source/tail distribution sanity
theorems and documentation for the finite channel-flow layer.

## Implemented Lean Surface

Added in `DkMath.Collatz.PetalBridge`:

```lean
theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
    (n : OddNat) (k : Nat) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k

theorem orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
    (n : OddNat) (k : Nat) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k 3 residue) = k

theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
    (r : Nat) (hr : 2 ≤ r) (n : OddNat) (k : Nat) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)

theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
    (r : Nat) (hr : 1 ≤ r) (n : OddNat) (k : Nat) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

The two `via_helper` theorems have the same statements as the existing
recursive count transitions, but their proofs now pass through:

```lean
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

with pointwise inputs:

```lean
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

## Mathematical Reading

The helper route fixes the intended finite channel-flow pattern:

```text
pointwise source residue transition
  -> source occupation count <= shifted-tail target occupation count
```

The recursive two-adic Petal channels are now instances of this generic route:

```text
recovery source
  -> outward-retention tail

continuation source
  -> next-retention tail
```

This matters because future residue-channel theorems no longer need custom
count inductions.  They only need a pointwise transition theorem.

## Depth-3 Sanity

The depth-`3` theorems pin down the generic distribution theorem at the familiar
`mod 8` layer:

```text
Sum_{residue < 8} sourceCount(residue) = k
Sum_{residue < 8} tailCount(residue) = k
```

This gives a readable bridge from named `mod 8` experiments back to the generic
`2^depth` distribution API.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status document now records:

```text
depth 3 source/tail distribution sanity
helper-routed recovery and continuation channels
finite channel-flow theorem chain
future Nat-inequality ratio layer note
```

## Inference

Checkpoint 099 turns the helper from an isolated theorem into the preferred
proof route.

The current layer can be summarized as:

```text
SourceDistribution:
  CountPow2 over labels 0..k-1

TailDistribution:
  TailCountPow2 over labels 1..k

Conservation:
  total source mass = k
  total tail mass = k

ChannelFlow:
  pointwise source-to-tail transition
    -> source occupation <= tail occupation

Recursive instances:
  recovery source <= outward-retention tail
  continuation source <= next-retention tail
```

This is a clean checkpoint before No.100.

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

Checkpoint 100 should probably be a consolidation checkpoint rather than a wide
new theorem expansion.

Recommended next work:

```text
1. Add a short docs/report summary for the finite channel-flow layer.

2. Optionally add very thin theorem aliases for the four-part chain:
   source partition
   tail partition
   pointwise-to-count helper
   recovery/continuation via-helper instances

3. Start the finite ratio layer only with Nat inequalities.
```

The first ratio experiments should avoid `ℚ` and `ℝ`:

```text
cell occupies at most half the window
  as 2 * count <= k

two channels occupy at most the window
  as countA + countB <= k
```

This keeps the next layer compatible with zero-window edge cases and avoids
coercion overhead.
