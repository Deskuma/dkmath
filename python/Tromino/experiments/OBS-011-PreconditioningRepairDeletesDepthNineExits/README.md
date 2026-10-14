# OBS-011 — Preconditioning Repair Deletes the Depth-Nine Exits

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-011 freezes the direct exchange-state maze comparison across the unique
W9 -> W10 one-flip transition from OBS-009/010.

The experiment compares the deterministic restore state immediately before the
same blocker:

```text
node 19 / step 16
```

on both sides of the diagonal flip:

```text
4-21 -> 5-17.
```

The main result is that the child maze is smaller, not larger, but both
depth-nine exits present in the parent disappear. The first surviving exits
move to depth ten.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-w10-maze-compare-v24/
```

Files:

```text
parent-profile.json
child-profile.json
comparison.json
```

Parent:

```text
seed = 11000009
required depth = 9
```

Child:

```text
seed = 12000006
required depth = 10
```

Both are evaluated under the endpoint repair harness at node 19 / step 16.

## Exit-depth shift

The first exit depths are:

```text
parent W9 : 9
child  W10: 10
```

At the decisive layers:

```text
depth 9:
  parent exits = 2
  child exits  = 0

depth 10:
  parent exits = 4
  child exits  = 5
```

Thus the W9 -> W10 transition is not explained by simple growth of the state
space.

Instead:

```text
the parent has two depth-nine exits;
the child deletes both of them;
new exits survive only at depth ten.
```

## Maze contraction

The complete explored state spaces through depth ten are:

```text
parent expanded unique states = 419838
child  expanded unique states = 279935
```

The child has fewer generated states at every positive layer.

Examples:

```text
depth 1 : 22 -> 21
depth 5 : 33106 -> 28103
depth 7 : 133259 -> 94950
depth 8 : 112768 -> 64469
depth 9 : 41085 -> 14976
depth 10: 4601 -> 657
```

So the depth increase is an **exit annihilation phenomenon inside a contracted
maze**, not a larger-search-space phenomenon.

## The blocker adjacency does not change

The neighbor set of blocker node 19 is identical in the parent and child.

The only graph edge change is:

```text
removed: 4-21
added:   5-17
```

Therefore the diagonal flip does not directly alter the adjacency of the
blocked node.

Its effect is mediated through the earlier deterministic restore trajectory.

## Preconditioning repair

The parent prefix before step 16 contains only:

```text
step 15 / node 18:
  repair depth 2
```

The child prefix gains an earlier repair:

```text
step 14 / node 17:
  (0 <-> 1) on {4}
  assigned color 1

step 15 / node 18:
  same depth-2 repair pattern as the parent
```

Consequently the colored states immediately before node 19 differ only at two
vertices:

```text
vertex 4 : parent 1 -> child 0
vertex 17: parent 3 -> child 1
```

This is the preconditioning step that changes the later repair maze.

## Kempe-component restructuring

At the blocker root, the parent has 22 available Kempe components and the child
has 21.

A particularly important parent pair of (0,1) components is:

```text
{4}
{8,9,10,11,12,15}
```

In the child these are replaced by the merged component:

```text
{4,8,9,10,11,12,15,17}
```

The first successful repair path changes accordingly.

Parent first move:

```text
(0 <-> 1) on {8,9,10,11,12,15}
```

Child first move:

```text
(0 <-> 1) on {4,8,9,10,11,12,15,17}
```

The parent first exit has depth 9 and footprint 13.
The child first exit has depth 10 and footprint 15.

This gives the current mechanistic picture:

```text
diagonal flip
-> earlier depth-1 repair at node 17
-> colors at vertices 4 and 17 change
-> Kempe components at node 19 reconnect
-> both depth-nine exits disappear
-> first surviving exit occurs at depth ten
```

## Collatz-like dynamical interpretation

The underlying flip is reversible, while the greedy restore trajectory is
history-sensitive and effectively directed.

This produces a useful qualitative picture:

```text
reversible local graph move
        |
        v
non-reversible deterministic restore trajectory
        |
        v
large jump in repair-depth observable
```

This resembles the non-monotone scalar behavior seen in Collatz-style dynamics,
but no arithmetic recurrence or equivalence with the Collatz map is claimed.

## What OBS-011 does not establish

It does not establish:

- that the displayed (0,1) component merge alone is sufficient for the depth
  jump;
- that both parent depth-nine exits fail for the same local reason;
- that the preconditioning mechanism generalizes to arbitrary depths;
- that the greedy restore order is canonical;
- any Four Color Theorem result;
- any Lean theorem.

## Next experiment

Extract **both** parent depth-nine exit paths, not only the first one, and replay
their exact Kempe moves against the child blocker state.

For each parent exit path:

1. list the complete nine-move sequence;
2. start from the child colored state at node 19 / step 16;
3. test each parent Kempe move for exact availability;
4. record the first unavailable move;
5. record the child Kempe component(s) of the same color pair that overlap the
   parent component.

The primary question is:

```text
Are both parent depth-nine exits destroyed by the same early component merge,
or by two distinct obstructions?
```

That is the next step toward isolating a minimal wall-deepening gadget.
