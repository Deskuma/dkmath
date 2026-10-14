# OBS-018 — Constraint Edge Sectorizes the W9 State Chamber

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-018 freezes the complete W10 blocker-state component scan and compares it
against the complete W9 component from OBS-017.

The W10 witness differs from W9 by the preserving diagonal flip:

```text
remove edge 4-21
add edge    5-17
```

The blocker remains node 19 at restore step 16.

## W10 complete component

The W10 admissible blocker-state component is complete and not truncated:

```text
states = 4
edges  = 3
degree range = 1..2
```

It is a simple path.

Repair-depth distribution:

```text
h = 9 : 3 states
h = 10: 1 state
```

There is no depth-eleven state in this component.

Every one-point state edge again satisfies:

```text
|delta h| <= 1
```

The three edge deltas are:

```text
0, +1, -1
```

Thus the W9 unit-slope observation survives an independent graph topology and a
much smaller admissible chamber.

## Exact shared sublandscape

The four W10 blocker-state projections occur verbatim inside the 32-state W9
component.

The exact correspondence is:

```text
W10 state 0  <-> W9 state  8   depth 9
W10 state 1  <-> W9 state 10   depth 9
W10 state 2  <-> W9 state 12   depth 10
W10 state 3  <-> W9 state 14   depth 9
```

The three W10 state edges map exactly to the induced W9 edges:

```text
8 -- 14 -- 12 -- 10
```

and the first-exit depth agrees at all four matched states.

So the W10 admissible component is not merely similar to part of W9: it is an
exact four-state state-transition sublandscape with the same height labels.

## The new edge acts as a state-space separator

At step 16, vertices 5 and 17 are already colored.

The added W10 edge `5-17` therefore imposes the proper-coloring constraint:

```text
color(5) != color(17)
```

Exactly 16 of the 32 W9 states satisfy this inequality.

Inside the W9 state graph, those 16 states split into four disconnected
four-state components:

```text
{1,3,5,7}       with (c5,c17) = (1,3)
{8,10,12,14}    with (c5,c17) = (3,1)
{16,17,18,19}   with (c5,c17) = (0,3)
{24,25,26,27}   with (c5,c17) = (0,1)
```

The actual W10 baseline state belongs to the second sector:

```text
{8,10,12,14}
```

and the complete W10 component is exactly that sector.

This gives a concrete mechanism for the chamber contraction:

```text
new properness edge
-> exclude equal-color endpoint states
-> split the former admissible chamber into sectors
-> deterministic restore lands in one sector
```

## Height preservation versus maze-volume contraction

Although the four shared states have identical first-exit depths in W9 and W10,
the repair-maze search volume changes strongly.

W9 shared-state expansion counts are approximately 419.8k states, while every
W10 state expands exactly:

```text
279935
```

states.

Thus this flip separates two effects in the witness:

```text
admissible chamber topology / repair-maze volume
```

can change substantially while:

```text
first-exit depth on the surviving shared sector
```

remains unchanged.

The full exit multiplicities are not preserved, so this is not a complete maze
isomorphism.

## Interpretation

The combined W9/W10 evidence now supports two distinct structural observations:

```text
1. admissible one-point state edges observed so far are unit-slope in h;
2. a local graph edge can sectorize the admissible state chamber while
   preserving h on the surviving shared sector.
```

Neither is yet promoted to a general theorem.

## Next experiment

Scan all 17 legal preserving one-flip neighbors of the W9 witness at the same
restore step.

For every neighbor, reconstruct the blocker state and enumerate its admissible
one-point recoloring component without the expensive repair-depth evaluation.

Record:

```text
flip edge removed / edge added
whether blocker adjacency changes
whether the restored blocker state changes
component state count / edge count
overlap with the 32-state W9 chamber
whether the child component is an induced W9 subgraph
new-edge endpoint color constraint
sector count predicted inside the W9 chamber
```

This tests whether the W10 sectorization mechanism is exceptional or a common
effect of preserving diagonal flips.
