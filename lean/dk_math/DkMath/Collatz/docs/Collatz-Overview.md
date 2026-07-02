# Collatz Overview

## Purpose

`DkMath.Collatz` formalizes a Collatz research route centered on the
accelerated odd-state map:

```text
T(n) = (3n + 1) / 2 ^ v2(3n + 1)
```

for odd natural states.

The package does not currently claim a proof of the Collatz conjecture.  Its
role is to build a verified observation language around:

```text
2-adic height
residue class
finite orbit window
occupation count
source/tail distribution
channel flow
```

This gives a controlled way to discuss where the Collatz map spends its finite
observation mass and how that mass moves from one residue channel to the next.

## The Accelerated Odd-State View

The ordinary Collatz map alternates between odd and even states.  The
accelerated map skips the even chain after `3n + 1`.

For an odd state `n`, define:

```text
s(n) = v2(3n + 1)
T(n) = (3n + 1) / 2 ^ s(n)
```

Then `T(n)` is odd again.

In Lean this surface is implemented around:

```lean
s
T
iterateT
sumS
```

The quantity `s(n)` is the number of powers of two peeled off at that step.
The finite sum

```text
sumS n k = s(n) + s(T n) + ... + s(T^(k-1) n)
```

is the accumulated 2-adic peeling in the first `k` accelerated steps.

## First Observation: Every Step Peels At Least One Factor

For odd `n`, `3n + 1` is even.  Therefore:

```text
1 <= s(n)
```

This gives the first lower bound:

```text
k <= sumS n k
```

In the PetalBridge file this becomes the count statement:

```lean
orbitWindowHeightCountGe_one_eq_window
```

Every entry in the observation window has height at least `1`.

## Residue Classes As Height Detectors

The bridge uses residue classes to read 2-adic heights.

For odd labels:

```text
height >= 2  <->  label % 4 = 1
height = 1   <->  label % 4 = 3
height >= 3  <->  label % 8 = 5
```

The exact mod `8` split refines the first layers:

```text
height = 2        <-> label % 8 = 1
height = 1        <-> label % 8 = 3 or 7
height >= 3       <-> label % 8 = 5
```

This is why residue channels are not just cosmetic.  They expose Collatz
height information without immediately leaving finite arithmetic.

## Observation Windows

`DkMath.Collatz.PetalBridge` defines a finite observation window:

```lean
OrbitWindow n k = Finset.range k
```

and labels it by the odd accelerated orbit:

```lean
oddOrbitLabel n i = (iterateT i n).val
orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
```

The window can be read as an ordered height profile:

```lean
orbitWindowHeightSeq n k
```

with:

```lean
(orbitWindowHeightSeq n k).sum = sumS n k
```

This connects the local finite profile to the existing accumulated-height API.

## From Counts To Distributions

The file then counts how often a finite window enters a chosen residue cell:

```lean
orbitWindowResidueCountPow2 n k depth residue
```

This counts labels `i < k` such that:

```text
oddOrbitLabel n i % 2^depth = residue
```

The shifted-tail analogue is:

```lean
orbitWindowResidueCountPow2Tail n k depth residue
```

which counts labels at times `i + 1` for `i < k`.

The No.100 conservation aliases are:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
```

They state:

```text
sum over all source residue cells = k
sum over all shifted-tail residue cells = k
```

This is a finite distribution layer.  Every label belongs to exactly one
residue cell at a fixed power-of-two depth.

## Channel Flow

The central bridge theorem is:

```lean
pow2ChannelFlow_of_pointwise
```

It says:

```text
If every source hit in one residue cell moves to a chosen shifted-tail
residue cell, then the source occupation count is bounded by the target
tail occupation count.
```

This turns pointwise residue arithmetic into count-level channel flow.

## What This Does Not Yet Do

This layer does not prove global convergence.

It also does not yet introduce:

```text
limits
probability
real-valued density
odd prime factor carriers
primitive factor events
```

The point is to keep the current layer finite and exact.  The next ratio layer
should first use natural-number inequalities such as:

```text
2 * count <= k
countA + countB <= k
m <= count
```

before introducing rational or real frequencies.
