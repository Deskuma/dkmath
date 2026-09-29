# OBS-010 — Unique Ascending Edge in the W9 One-Flip Neighborhood

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-010 freezes the complete one-flip neighborhood census around the
frontier-amplified W9 witness from OBS-008.

The experiment exhaustively evaluates every legal planted-color-preserving
diagonal flip from that graph.

The main result is that the previously observed W9 -> W10 move is unique among
all immediate legal preserving flips.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-oneflip-neighborhood-v24/
```

Source witness:

```text
python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json
seed = 11000009
required depth = 9
```

Evaluation parameters:

```text
max_depth           = 10
node_limit          = 6000000
intermediate_policy = endpoint
```

## Complete neighborhood census

The source graph has exactly 17 legal planted-color-preserving one-flip
neighbors.

All 17 neighbors resolve under ceiling ten.

Depth histogram:

```text
depth 10 : 1
depth  9 : 0
depth  8 : 3
depth  7 : 3
depth  6 : 6
depth  5 : 2
depth  4 : 2
```

Therefore the source W9 graph has no one-flip neighbor that remains at depth
nine.

Its local depth picture is:

```text
             W10  (1)
              ^
              |
              W9  (source)
            / | \
      W8/W7/W6/W5/W4  (16)
```

This is a complete statement about the immediate legal preserving flip
neighborhood under the present harness.

## Unique ascending edge

The unique depth-ten neighbor is produced by:

```text
[4,21,5,17]
```

or equivalently the diagonal replacement:

```text
4-21 -> 5-17
```

Face replacement:

```text
remove {4,5,21}
remove {4,17,21}

add    {4,5,17}
add    {5,17,21}
```

The resulting neighbor is replay-verified at required depth ten.

No other legal preserving one-flip neighbor reaches depth nine or ten.

## Same blocker, different maze depth

For every one of the 17 neighbors, the depth-minus-one failure occurs at the
same restore location:

```text
node = 19
step = 16
```

Thus the one-flip perturbations do not move the critical restore location.
Instead they change the depth of the exchange-state maze attached to the same
blocked node.

Observed one-flip depths span:

```text
4, 5, 6, 7, 8, 10
```

while the source itself has depth nine.

This makes repair depth highly non-smooth on the local flip graph.

## Geometry of the ascending flip

The unique ascending flip is not incident to blocker node 19.

In the W9 source graph, the four flip vertices have graph distances from node
19:

```text
4  : 1
5  : 1
17 : 1
21 : 2
```

So the depth-raising mutation is still contained entirely in the radius-two
neighborhood of the blocker, but it changes a diagonal one shell away rather
than changing an edge incident directly to node 19.

## V4 color observation

Every legal preserving one-flip quadrilateral in this census uses all four
planted colors.

Consequently, under the identification

```text
V4 ~= ZMod 2 x ZMod 2,
```

the old and new diagonals automatically have the same XOR/color difference.

For the unique ascending flip:

```text
colors(4,21) = (3,0)
colors(5,17) = (1,2)

3 xor 0 = 1 xor 2 = 3
```

But this property holds for all 17 legal preserving flips, so V4 color-difference
conservation alone does not distinguish the ascending edge.

The discriminating structure must be finer than the four-color labels.

## Collatz-like qualitative analogy

The local depth motion resembles a Collatz-style directed landscape only as a
qualitative analogy:

- a simple local operation can cause a large jump in a scalar complexity;
- nearby states may fall sharply or rise;
- the scalar is not monotone along local moves.

No Collatz theorem, conjugacy, probabilistic model, or arithmetic equivalence is
claimed here.

The useful idea is to study the flip graph as a discrete dynamical state space
with repair depth as an observable.

## What OBS-010 does not establish

It does not establish:

- that W9 is globally isolated among all 24-vertex maps;
- that the unique local ascending edge is unique under another restore order;
- that repair depth obeys a Collatz recurrence;
- that the W9 -> W10 diagonal is a universal wall gadget;
- that radius two suffices at arbitrary depth;
- any Four Color Theorem consequence;
- any Lean theorem.

## Next experiment

The next task is to compare the **exchange-state repair maze** at the same
critical location before and after the unique ascending flip.

Compare:

```text
parent : W9  / seed 11000009
child  : W10 / unique move [4,21,5,17]
blocker: node 19 / step 16
```

Measure BFS layer populations, exit counts, Kempe-component branching, and the
first successful repair path.

The goal is to identify what the one diagonal flip changes inside the repair
state graph that closes every depth-nine exit and forces the first exit to
depth ten.
