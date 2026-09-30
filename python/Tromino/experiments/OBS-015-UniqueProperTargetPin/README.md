# OBS-015 — Vertex 4 Is the Unique Proper Target-Color Pin Site

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-015 freezes the target-color pin scan following OBS-014.

The parent W9 graph and blocker state are fixed at:

```text
node 19 / step 16
target exit color = 0
```

Every unlocked colored blocker neighbor whose current color is nonzero was
individually recolored to color 0.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-target0-pin-scan-v24/
```

Baseline:

```text
first exit depth = 9
depth-9 exits    = 2
depth-10 exits   = 4
```

Candidate vertices:

```text
4, 5, 8, 9, 10, 13, 17, 18
```

## Result

The scan reports:

```text
raising_vertices = [4]
invalid_vertices = [5,8,9,10,13,17,18]
```

No valid target-color pin remains at depth nine or lowers the depth.

For vertex 4:

```text
4 : 1 -> 0
valid
first exit depth = 10
depth-9 exits    = 0
depth-10 exits   = 4
```

Every other candidate target-color pin is improper.

## Why the other target-zero pins are invalid

At the blocker state, existing colored zero vertices include:

```text
12, 14, 15, 16
```

Among the tested blocker neighbors:

```text
5  -> conflicts with zero vertex 14
8  -> conflicts with zero vertices 12 and 15
9  -> conflicts with zero vertex 12
10 -> conflicts with zero vertex 12
13 -> conflicts with zero vertex 14
17 -> conflicts with zero vertex 15
18 -> conflicts with zero vertices 12 and 15
```

Vertex 4 is the only nonzero tested blocker neighbor with no adjacent
already-colored zero vertex.

Therefore the target-zero scan has only one proper one-point intervention.

## Interpretation

The statement

```text
raising_vertices = [4]
```

must not be over-interpreted as showing that vertex 4 wins a dynamical
competition among several valid zero-pin sites.

There is only one proper target-zero site in this blocker state.

So the stronger supported statement is:

```text
vertex 4 is the unique proper one-point target-zero pin site,
and that unique valid pin raises the first exit depth from 9 to 10.
```

This reveals a feasibility gate before the repair-maze dynamics:

```text
proper-coloring constraint
-> admissible one-point recolor sites
-> repair-depth effect
```

## Local color flexibility

Looking beyond target color 0, some blocker neighbors admit other proper
single-vertex recolorings.

Examples from the fixed parent blocker state:

```text
4  : 1 -> {0,2}
5  : 3 -> {2}
9  : 1 -> {2}
10 : 1 -> {2}
13 : 3 -> {1,2}
14 : 0 -> {1,2}
15 : 0 -> {2}
17 : 3 -> {2}
```

while vertices 8, 12, and 18 have no proper alternative color.

## Next experiment

Enumerate all proper one-point recolorings of unlocked colored blocker
neighbors, not only recolorings to the current exit target color 0.

For every valid one-point state mutation measure:

```text
old color -> new color
first exit depth
exit counts
maze size
whether the recolored vertex appears in either baseline depth-nine path
```

This separates two questions:

1. Is depth raising special to target-color pinning?
2. Is vertex 4 special even among all proper one-point recolorings?
