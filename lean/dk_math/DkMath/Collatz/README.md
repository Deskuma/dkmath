# DkMath.Collatz

`DkMath.Collatz` is the DkMath formalization workspace for the accelerated
Collatz map on odd natural states.

The current package is not only a direct attempt to prove the Collatz
conjecture.  It is a structured observation program:

```text
odd state dynamics
  -> 2-adic height
  -> residue channels
  -> finite observation windows
  -> source/tail distributions
  -> finite channel flow
```

The most recent milestone is the finite channel-flow layer in
`DkMath.Collatz.PetalBridge`.  It turns pointwise residue transitions into
count-level statements over finite windows, without using limits,
probability, or real-valued frequencies.

## Module Entry Points

```text
DkMath.Collatz.Basic
DkMath.Collatz.V2
DkMath.Collatz.Accelerated
DkMath.Collatz.Shift
DkMath.Collatz.PetalBridge
DkMath.Collatz.Collatz2K26
```

### `DkMath.Collatz.Basic`

Defines the basic Collatz surface:

```lean
C
OddNat
threeNPlusOne
```

This is the lowest-level arithmetic layer.

### `DkMath.Collatz.V2`

Provides the local 2-adic valuation vocabulary used by the accelerated map.

Important names include:

```lean
v2
v2_3n_plus_1_ge_1
v2_shift_invariant
```

This file is the arithmetic source of the fact that every odd accelerated
Collatz state peels at least one factor of `2`.

### `DkMath.Collatz.Accelerated`

Defines the accelerated odd-state Collatz map:

```lean
s n = v2 (3 * n + 1)
T n = (3 * n + 1) / 2 ^ s n
iterateT
sumS
driftReal
```

This is the dynamical core.

### `DkMath.Collatz.Shift`

Records the block-shift / petal-cartography approach.

This older approach studies how the valuation signal behaves under shifts by
powers of two:

```text
n -> n + 2^k * m
```

The guiding idea is that many differences do not appear everywhere; they
concentrate around singular 2-adic ridges.

### `DkMath.Collatz.PetalBridge`

This is the current main bridge.

It packages finite windows of the accelerated orbit and connects them to
Petal-style counting:

```lean
OrbitWindow
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
orbitWindowResidueCountPow2
orbitWindowResidueCountPow2Tail
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

The central No.100 layer is:

```text
Source distribution:
  sum of all source residue counts = window size

Tail distribution:
  sum of all shifted-tail residue counts = window size

Channel flow:
  pointwise source-to-tail residue transition
    -> source count <= target tail count
```

### `DkMath.Collatz.Collatz2K26`

Integration file for the 2026 Collatz cartography project.

It imports the main Collatz files and marks the package-level surface.

## Main Documentation

Read these in order:

```text
docs/Collatz-Overview.md
docs/Collatz-Package-Structure.md
docs/Collatz-FiniteChannelFlow-100.md
docs/Collatz-FiniteRatioRetention-101.md
docs/Collatz-PetalBridge-Guide.md
docs/Collatz-PetalBridge-Status.md
```

Older and experimental notes:

```text
docs/CollatzCartography.md
docs/CollatzCartography-ja.md
docs/IMPLEMENTATION_REPORT_20260130.md
docs/AUXILIARY_LEMMA_COMPLETION_20260130.md
docs/SORRY_CLEANUP_PROGRESS_20260130.md
```

Petal-side companion:

```text
../Petal/docs/Petal-CollatzBridge.md
```

## What Was Achieved At Checkpoint 100?

Checkpoint 100 closes a finite, natural-valued observation layer.

The important Lean aliases are:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

They summarize earlier technical theorems:

```lean
orbitWindowResidueCountPow2_sum_eq_window
orbitWindowResidueCountPow2Tail_sum_eq_window
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

The mathematical point is simple:

```text
Every label in a finite window occupies exactly one residue channel.
If a pointwise transition sends one channel into another channel,
then the occupation count of the source channel is bounded by the
occupation count of the target shifted-tail channel.
```

This is not yet a proof of Collatz termination.  It is a verified framework
for talking about finite channel mass and its movement under the accelerated
map.

## Next Direction

The next natural layer is a finite ratio layer, but still using natural-number
inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

This avoids division by zero and coercion overhead.  Rational or real
frequencies can be introduced later if the finite inequality layer repeatedly
needs them.

Checkpoint 101 begins that layer with:

```lean
AtMostHalf
AtMostRatioNat
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
```

See:

```text
docs/Collatz-FiniteRatioRetention-101.md
```
