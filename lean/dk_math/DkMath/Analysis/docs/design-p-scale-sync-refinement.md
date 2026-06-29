# Design: p-Scale and Sync Refinement

## Purpose

This note records the design rule for comparing phase scales of the form
`1 / k`, especially prime scales `1 / p`.

The point is not merely that `k * (1 / k) = 1`. That identity records a
single closed total. The harder design question is how different closed
scales are compared on the same conserved boundary.

This note keeps the discussion pre-geometric. It does not use circle, angle,
arc, or Euclidean rotation as input data. Those are later readings.

## Scale Versus Total

For a positive natural number `k`, the statement

```text
k * (1 / k) = 1
```

means that a `k`-step scale closes after one total cycle.

However, comparing `1 / k` and `1 / l` is not only a question of total size.
It is a question of refinement structure.

```text
1/k:
  a convention for cutting one conserved cycle into k equal steps

comparison:
  whether two conventions live in the same refinement family, or only meet
  after a common refinement
```

For example, `1 / 2` and `1 / 4` belong to the same dyadic refinement family,
because a `1 / 2` step is two `1 / 4` steps.

By contrast, `1 / 4` and `1 / 5` do not refine one another. They meet on the
common refinement `1 / 20`.

## Sync Cycle

The comparison unit should be a sync cycle.

For two scales `k` and `l`, define the sync length as:

```text
SyncLength k l = Nat.lcm k l
```

Then the lift factors are:

```text
syncLiftLeft k l  = Nat.lcm k l / k
syncLiftRight k l = Nat.lcm k l / l
```

Meaning:

```text
k-scale reaches the sync cycle after syncLiftLeft k l local cycles.
l-scale reaches the sync cycle after syncLiftRight k l local cycles.
```

If `k` and `l` are coprime, then the lift factors are exchanged:

```text
Nat.lcm k l / k = l
Nat.lcm k l / l = k
```

This is the finite synchronization rule: one scale's number of divisions
becomes the other scale's number of local cycles inside the shared sync
cycle.

## Common Refinement

The correct comparison of `1 / k` and `1 / l` is:

```text
1/k step:
  syncLiftLeft k l ticks of the 1/(lcm k l) scale

1/l step:
  syncLiftRight k l ticks of the 1/(lcm k l) scale
```

Example:

```text
k = 4
l = 5
lcm k l = 20

1/4 step:
  5 ticks of 1/20

1/5 step:
  4 ticks of 1/20
```

Thus coprime scales are not incompatible. They are jointly embedded into a
larger finite sync scale.

## Primitive Scale

A prime scale should be treated as a primitive channel, not as a refinement
of smaller nontrivial scales.

At the star-action level, the general predicate should be:

```text
IsPrimitiveScale k r:
  starPow k r = one
  and for every n with 0 < n < k, starPow n r != one
```

The non-primitive finite-order predicate is:

```text
IsScale k r:
  starPow k r = one
```

For prime `p`, a nontrivial `p`-scale is primitive because `p` has no
nontrivial positive divisors.

## Star-Action Reading

The two-coordinate star product should read a scale as a finite-order unit
kernel.

```text
unit:
  q2 r = 1

period:
  starPow k r = one

primitive:
  0 < n < k -> starPow n r != one
```

For an initial point `z`, the scale orbit is:

```text
n |-> starPow n r ⋆ z
```

If `starPow k r = one`, then the orbit closes after `k` steps. If `r` is
primitive and the orbit is nondegenerate, this is the first closing time.

## Realization Layers

The design should separate three layers.

```text
combinatorial scale:
  Fin k and successor modulo k

star-action scale:
  a unit kernel r with starPow k r = one

realization scale:
  existence of such primitive unit kernels in a semantic model
```

The first layer always exists. The second layer may assume a finite-order
kernel. The third layer is mathematically heavier.

In particular, proving existence of primitive `p`-scales for arbitrary prime
`p` should not be attempted inside the current nonnegative rational layer.
For `p > 4`, coordinates generally require signed and algebraic or complex
semantic data. The natural semantic bridge is the complex-root-of-unity
interpretation of the two-coordinate star product:

```text
(C, S) <-> C + i S
star <-> complex multiplication
q2 <-> squared norm
primitive p-scale <-> primitive p-th root of unity
```

This is a realization theorem, not a prerequisite for the combinatorial and
star-action APIs.

## Finite And Infinite Synchronization

Every finite family of positive scales has a sync cycle, given by the lcm of
all denominators.

```text
finite family:
  common sync cycle exists
```

The infinite family of all prime scales has no finite natural sync length.
This marks a boundary:

```text
finite:
  common period exists

infinite primes:
  no finite common period exists
```

This distinction should be preserved. It is a possible later bridge toward
prime-wave, Euler-product, or aperiodicity phenomena.

## Degenerate Zero Orbit

The zero state must be separated from primitive orbit analysis.

For a star action:

```text
r ⋆ 0 = 0
```

Therefore every scale collapses to the same constant orbit at zero.

```text
zero orbit:
  all cycles collapse

nonzero orbit:
  period and primitive scale can be read
```

Lean predicates about primitive orbits should include a nondegeneracy
hypothesis such as:

```text
z != 0
```

or, in DkMath boundary language:

```text
q2 z != 0
```

The zero orbit is not a counterexample to primitive scale. It is a singular
case where all period information has collapsed.

## Implementation Order

The safe implementation order is:

```text
1. define IsScale k r and IsPrimitiveScale k r;
2. prove primitive scale implies minimal period k;
3. prove divisibility extraction: if k divides m, then an m-scale can produce
   a k-scale by powering;
4. define SyncLength and sync-lift factors by Nat.lcm;
5. prove common-refinement embedding for two finite scales;
6. prove the prime shortcut: a nontrivial p-scale is primitive when p is
   prime;
7. only later, prove semantic existence of primitive p-scales.
```

The immediate Lean target should be the combinatorial and star-action API.
Existence theorems for arbitrary prime scales belong to a later semantic
realization layer.

## Naming Guidance

Preferred names:

```text
IsScale
IsPrimitiveScale
SyncLength
syncLiftLeft
syncLiftRight
CommonRefinement
PrimitiveUnitKernel
FiniteOrderKernel
StarCycle
```

Avoid angle or Euclidean vocabulary in the core scale API. A later bridge may
read the phase index `j / k` as a Euclidean angle, but the core object is:

```text
j-th phase of the k-scale
```

and comparisons are performed by sync lift into a common refinement.
