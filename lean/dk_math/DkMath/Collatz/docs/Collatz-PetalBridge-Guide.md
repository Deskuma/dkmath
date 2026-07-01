# Collatz PetalBridge Guide

## Why PetalBridge Exists

`DkMath.Collatz.PetalBridge` connects accelerated Collatz dynamics to the
Petal observation style used elsewhere in DkMath.

The Petal side already has language for:

```text
finite ranges
addresses
occupation counts
separation vs collision
boundary and channel behavior
```

The Collatz side has:

```text
odd states
2-adic height
accelerated transition
finite orbit segments
```

`PetalBridge` is the file where these languages meet.

## Basic Objects

### `OrbitWindow`

```lean
OrbitWindow n k
```

This is the finite observation window of length `k`.

It is definitionally:

```text
Finset.range k
```

### `oddOrbitLabel`

```lean
oddOrbitLabel n i
```

This is the natural value of the `i`-th accelerated odd state:

```text
(iterateT i n).val
```

### `orbitWindowHeight`

```lean
orbitWindowHeight n i
```

This is:

```text
v2 (3 * oddOrbitLabel n i + 1)
```

It is the local 2-adic peeling height.

### `orbitWindowHeightSeq`

```lean
orbitWindowHeightSeq n k
```

This is the ordered list of the first `k` height values.

The bridge theorem:

```lean
orbitWindowHeightSeq_sum_eq_sumS
```

connects the ordered list back to the accumulated Collatz height:

```text
(orbitWindowHeightSeq n k).sum = sumS n k
```

## Separation And Collision

The bridge includes a finite split:

```lean
OrbitWindowSeparated n k
OrbitWindowCollision n k
orbitWindowSeparated_or_collision
```

This reads:

```text
either the first k odd orbit labels are separated,
or there is a collision inside the window
```

The Petal reading:

```text
separated labels support independent finite counting
collision is an obstruction to that independent route
```

The Collatz reading:

```text
collision means the accelerated odd state has merged/folded
```

This split is finite.  It is not a global convergence theorem.

## Height Counts

The file defines exact and threshold height counts:

```lean
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountEqTail
orbitWindowHeightCountGeTail
```

These are finite `Nat` counts.

They support layer-cake style bounds such as:

```lean
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

The important Collatz floor is:

```lean
orbitWindowHeightCountGe_one_eq_window
```

Every odd accelerated state has height at least `1`.

## Residue Counts

Named residue counts exist for low layers:

```lean
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod4EqThree
orbitWindowResidueCountMod8EqOne
orbitWindowResidueCountMod8EqThree
orbitWindowResidueCountMod8EqFive
orbitWindowResidueCountMod8EqSeven
```

The generic power-of-two count is:

```lean
orbitWindowResidueCountPow2 n k depth residue
```

The shifted-tail version is:

```lean
orbitWindowResidueCountPow2Tail n k depth residue
```

This generic surface is the current preferred route for new residue-channel
work.

## Distribution Conservation

Checkpoint 100 exposes the conservation laws as conceptual aliases:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
```

These say that every finite source or shifted-tail window is fully partitioned
by its `2^depth` residue cells.

This gives the exact finite analogue of:

```text
total distribution mass = window size
```

but still in `Nat`.

## Channel Flow

The main helper is:

```lean
pow2ChannelFlow_of_pointwise
```

Use it when you have a pointwise theorem of the form:

```text
for all i < k,
  source cell condition at i
    -> target tail cell condition at i + 1
```

The helper returns:

```text
source cell count <= target tail cell count
```

## Depth Refinement

Checkpoint 102 adds the recursive residue-cell split.

The pointwise theorem is:

```lean
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
```

It says that a valid residue cell at depth `depth` has exactly two children at
depth `depth + 1`:

```text
residue
residue + 2^depth
```

The count-level theorem is:

```lean
orbitWindowResidueCountPow2_refine_succ
```

It upgrades the pointwise split to finite window occupation counts:

```text
count(parent cell)
  = count(left child) + count(right child)
```

The retention-channel specialization is:

```lean
orbitWindowRetentionMass_split
```

This reads:

```text
retention mass at depth r
  = recovery sibling mass at depth r+1
    + continuation sibling mass at depth r+1
```

Use this theorem when an argument needs to show that recovery and continuation
are not independent extra mass.  They are the two subcells of the previous
retention cylinder.

Checkpoint 103 adds the shifted-tail counterpart:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
```

So the same reading is available in the receiving window:

```text
tail retention mass at depth r
  = tail recovery sibling mass at depth r+1
    + tail continuation sibling mass at depth r+1
```

The useful forcing aliases are:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

Use these names when the argument is conceptually about mass flow from the
source window into the shifted-tail window.  Use the split theorems when the
argument is about decomposing a retention cylinder into its two child cells.

## Finite Half Criteria

Checkpoint 104 connects the split theorems to `AtMostHalf`.

The source criterion is:

```lean
atMostHalf_continuation_of_continuation_le_recovery
```

The tail criterion is:

```lean
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

Both have the same reading:

```text
continuation <= recovery
  -> continuation is at most half of retention
```

There are also recovery-budget variants:

```lean
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

These do not prove the comparison condition.  They make the next target
explicit: find a structural reason why continuation is no larger than recovery,
or why recovery covers at least half of retention.

## Comparison Predicates

Checkpoint 105 names the missing comparison conditions:

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

The predicate-facing half criteria are:

```lean
atMostHalf_continuation_of_recoveryDominates
atMostHalf_tailContinuation_of_tailRecoveryDominates
atMostHalf_continuation_of_recoveryCoversHalf
atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
```

Use these names when a later proof has produced a comparison hypothesis and
wants to consume it without unfolding recovery/continuation counts.

This is the theorem to reach for before writing a custom induction over `k`.

## Recursive Petal Residues

The current recursive two-adic Petal channels are:

```lean
twoAdicRetentionResidue
twoAdicRecoverySiblingResidue
twoAdicContinuationSiblingResidue
```

The count-level recursive instances are now available through helper-routed
theorems:

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
```

This fixes the intended proof route:

```text
residue formula
  -> pointwise orbit-label transition
  -> finite channel-flow count inequality
```

## How To Add A New Channel Theorem

For a new residue channel:

1. Prove the pointwise transition:

```text
if oddOrbitLabel n i is in source cell A,
then oddOrbitLabel n (i + 1) is in tail cell B.
```

2. Apply:

```lean
pow2ChannelFlow_of_pointwise
```

3. State a named theorem for the channel:

```text
sourceChannelCount <= tailChannelCount
```

Avoid writing a fresh count induction unless the helper does not fit.

## Next Work

The next layer should probably introduce finite ratio witnesses, but still as
natural-number inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

Only later should this become rational or real frequency.

Checkpoint 101 starts this layer with:

```lean
AtMostHalf
AtMostRatioNat
```

and names the retention-channel masses:

```lean
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
```

Use these names when a theorem is conceptually about low-peeling retention,
rather than writing the raw residue-count expression every time.
