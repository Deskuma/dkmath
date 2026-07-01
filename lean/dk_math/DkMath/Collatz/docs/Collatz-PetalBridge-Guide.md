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
