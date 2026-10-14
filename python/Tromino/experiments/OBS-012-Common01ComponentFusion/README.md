# OBS-012 — Common (0,1) Component Fusion Kills Both Depth-Nine Exits

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-012 freezes the exit-path replay experiment following OBS-011.

The parent W9 blocker state has exactly two exits at repair depth nine. The
child W10 blocker state has none.

Both parent exit paths fail when replayed on the child, and both failures are
caused by enlargement of a parent (0,1) Kempe component through the vertices
`4` and `17`.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-w10-exit-compare-v24/
```

Files:

```text
parent-exits.json
child-exits.json
comparison.json
```

Baseline:

```text
parent W9: depth-9 exits = 2
child W10 : depth-9 exits = 0
```

Neither search was truncated.

## Exit 0

The first parent depth-nine exit begins with:

```text
(0 <-> 1) on {8,9,10,11,12,15}
```

On the child blocker state, this exact component no longer exists.

Instead the overlapping (0,1) component is:

```text
{4,8,9,10,11,12,15,17}
```

which strictly contains the parent component.

Therefore:

```text
exact prefix length = 0
first divergence    = move 0
```

The first shallow exit is destroyed immediately at its entrance.

## Exit 1

The second parent depth-nine exit begins:

```text
move 0: (0 <-> 1) on {14}
move 1: (0 <-> 2) on {3,12}
```

Both moves remain exactly available in the child.

The third parent move is:

```text
(0 <-> 1) on {3,8,11,15}
```

but after the same first two moves in the child, the overlapping component is:

```text
{3,4,8,11,15,17}
```

Again the child component strictly contains the parent component.

Therefore:

```text
exact prefix length = 2
first divergence    = move 2
```

The second shallow exit survives two moves and is then destroyed by the same
kind of (0,1) component enlargement.

## Common mechanism

The two parent exits fail at different positions but by one common structural
mechanism:

```text
parent (0,1) component
+ vertices 4 and 17
-> larger child (0,1) component
-> exact parent Kempe swap unavailable
-> depth-nine exit deleted
```

This sharpens the mechanism from OBS-011:

```text
4-21 -> 5-17
-> earlier step-14 repair at node 17
-> blocker-state colors change at vertices 4 and 17
-> (0,1) Kempe components reconnect
-> both depth-nine exits disappear
-> first child exit occurs at depth ten
```

## Important limitation

This experiment establishes a common obstruction for the two known parent
depth-nine exit paths.

It does **not** yet establish that the component fusion is sufficient by itself
to force depth ten.

The graph topology and the deterministic blocker state changed together along
the real W9 -> W10 trajectory.

A controlled intervention is required.

## Next experiment — 2x2 topology/state intervention

At node 19 / step 16, separate:

```text
P-graph = parent W9 adjacency
C-graph = child W10 adjacency

P-state = parent colored state
C-state = child colored state
```

Evaluate the repair maze for crossed combinations when the synthetic colored
state is proper and satisfies the blocker invariant:

```text
P-graph + P-state  = baseline depth 9
P-graph + C-state  = state-only intervention
C-graph + C-state  = baseline depth 10
C-graph + P-state  = topology-only intervention, if valid
```

The crossed child-graph + parent-state combination must not be interpreted if
the added edge `5-17` makes that coloring improper.

The central question is whether:

```text
P-graph + C-state
```

already moves the first exit from depth nine to depth ten. If so, the
preconditioned blocker state is sufficient within the fixed parent topology to
produce the depth jump.
