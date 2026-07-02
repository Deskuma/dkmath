# Petal And Collatz Bridge

## Purpose

This document records how the Petal package connects to the Collatz package.

The bridge is implemented on the Collatz side:

```text
DkMath.Collatz.PetalBridge
```

but the conceptual reason it works comes from Petal-style finite observation:

```text
finite range
address / residue cell
occupation count
separation or collision
channel movement
```

## Petal View

The Petal package studies finite structured observation surfaces.

In number-theory work this appears as:

```text
GN kernels
boundary / beam / gap separation
primitive factor support
range-family labels
obstruction when labels collide
```

The Collatz bridge uses the same kind of language, but the labels are not GN
terms.  They are accelerated Collatz odd orbit labels:

```text
oddOrbitLabel n i = value of T^i(n)
```

## Collatz View

The accelerated Collatz map has a natural Petal-like coordinate:

```text
2-adic residue class modulo 2^depth
```

At a fixed depth, all odd orbit labels fall into exactly one residue cell.

This allows Collatz to be read as:

```text
finite source distribution
finite shifted-tail distribution
pointwise channel transition
count-level channel flow
```

## The Bridge Object

The finite window is:

```lean
OrbitWindow n k = Finset.range k
```

The label function is:

```lean
oddOrbitLabel n i
```

The height function is:

```lean
orbitWindowHeight n i
```

The generic source count is:

```lean
orbitWindowResidueCountPow2 n k depth residue
```

The generic shifted-tail count is:

```lean
orbitWindowResidueCountPow2Tail n k depth residue
```

## No.100 Finite Channel-Flow Layer

The Collatz side exposes the theorem chain with conceptual names:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

Petal reading:

```text
source distribution total is conserved
tail distribution total is conserved
pointwise motion of labels induces count-level channel flow
```

Collatz reading:

```text
residue cells of odd orbit labels form a finite distribution
one-step residue transitions push source mass into tail cells
```

## Why This Matters For Petal

Petal theory often separates two cases:

```text
labels remain separated
labels collide and the independent route closes as False
```

Collatz orbit windows have the same finite split:

```lean
OrbitWindowSeparated
OrbitWindowCollision
orbitWindowSeparated_or_collision
```

This makes Collatz a testbed for Petal observation logic:

```text
finite observation window
label uniqueness or collision
address cells
occupation counts
channel transitions
obstruction when the independent counting picture breaks
```

## Relation To Existing Petal RangeFamily

`DkMath.Petal.RangeFamily` provides a range-indexed observation layer:

```text
I = Finset.range k
qOf i = selected label at index i
```

It can express:

```text
pairwise label separation
same label at two distinct indices -> False
```

The Collatz bridge uses this spirit, but specializes the labels to the
accelerated odd orbit.

## What Is Not Yet Connected

The Collatz bridge currently remains 2-adic.

It does not yet connect Collatz channel occupation to:

```text
GN primitive factors
odd prime carriers
Zsigmondy witnesses
ABC support/radical estimates
```

Those are later chapters.

The immediate next layer should be finite ratio witnesses, still written as
natural-number inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

This keeps the Petal-Collatz bridge elementary before it is attached to
heavier factor-support machinery.

## Reading Pointers

Collatz side:

```text
DkMath/Collatz/README.md
DkMath/Collatz/docs/Collatz-Overview.md
DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Petal side:

```text
DkMath/Petal/docs/Petal-Overview.md
DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
```
