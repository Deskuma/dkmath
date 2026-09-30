# OBS-016 — Admissible One-Point State Landscape

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-016 freezes the complete scan of statically proper one-vertex recolorings
of unlocked colored neighbors of blocker node 19 at restore step 16.

The parent W9 blocker state has first exit depth nine.

The experiment asks how every admissible one-point state mutation changes that
depth.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-single-recolor-scan-v24/
```

Baseline:

```text
first exit depth = 9
depth-9 exits    = 2
depth-10 exits   = 4
baseline exit color = 0
```

## Static properness versus Missing-Color admissibility

There are eleven statically proper one-point recolor candidates.

Only three also preserve the Missing-Color invariant at the blocker state:

```text
4  : 1 -> 0   first exit depth 10
13 : 3 -> 1   first exit depth 8
14 : 0 -> 1   first exit depth 8
```

The remaining eight statically proper recolorings all change a vertex to color
2 and immediately break the Missing-Color invariant.

Thus the valid one-step landscape around W9 is:

```text
       4:1->0
          |
          v
         d10

d8 <- 13:3->1   W9/d9   14:0->1 -> d8
```

More precisely:

```text
raising_recolors:
  4 : 1 -> 0

lowering_recolors:
  13 : 3 -> 1
  14 : 0 -> 1

same_depth_recolors:
  none
```

## Color 2 is the missing future color

At this restore state, every remaining vertex

```text
19, 20, 21, 22, 23
```

has the same observed colored-neighbor palette:

```text
{0,1,3}
```

Therefore color 2 is absent from every remaining-vertex palette.

Every statically proper recoloring to color 2 inserts that missing color into at
least blocker node 19, producing:

```text
{0,1,2,3}
```

and violating the Missing-Color invariant.

Some recolorings to 2 simultaneously saturate additional future vertices:

```text
5 -> 2  : nodes 19,21,22
10 -> 2 : nodes 19,23
13 -> 2 : nodes 19,22
14 -> 2 : nodes 19,22
15 -> 2 : nodes 19,22
17 -> 2 : nodes 19,21
```

So the invariant is acting as a genuine state-space gate, not merely as a
post-hoc solver check.

## Three-way local dynamics

Among valid one-point moves there is no neutral move.

The repair-depth observable changes by exactly one:

```text
4 : 1 -> 0   gives 9 -> 10
13: 3 -> 1   gives 9 -> 8
14: 0 -> 1   gives 9 -> 8
```

This is the first complete local state-neighborhood around the W9 blocker.

It gives a small directed-looking height landscape even though the underlying
valid recoloring moves themselves are reversible whenever both endpoint states
remain admissible.

## What OBS-016 does not establish

It does not establish:

- that every admissible state has only +/-1 depth changes;
- that repair depth is a discrete Morse function;
- that the admissible state graph is acyclic;
- that color 2 remains globally missing away from this blocker state;
- any Collatz recurrence;
- any Four Color Theorem consequence;
- any Lean theorem.

## Next experiment — full admissible state component

Keep the parent graph, restore step, remaining set, and non-blocker-neighbor
colored vertices fixed.

Use single-vertex recoloring edges among unlocked colored blocker neighbors,
but retain only states that are:

```text
properly colored
and
Missing-Color invariant valid.
```

Enumerate the entire connected component containing the W9 blocker state.

Then evaluate repair depth at every component state.

A static enumeration before the expensive repair evaluation finds:

```text
32 admissible states
degree range 1..5
mean degree 3
no reachable state uses color 2 on the mutable blocker neighbors
```

The next experiment will verify the repair-depth distribution over all 32
states and expose the first concrete admissible state-transition landscape.
