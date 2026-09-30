# OBS-013 — Blocker State Alone Reproduces the Depth Jump

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-013 freezes the topology/state intervention experiment following OBS-012.

The experiment separates graph topology from the colored restore state at the
same blocker:

```text
node 19 / step 16
```

The central result is that the child blocker state, transplanted onto the
parent W9 graph, is sufficient to move the first repair exit from depth nine to
depth ten.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-w10-intervention-v24/
```

Files:

```text
Pgraph_Pstate.json
Pgraph_Cstate.json
Cgraph_Pstate.json
Cgraph_Cstate.json
comparison.json
```

Notation:

```text
Pgraph = parent W9 graph
Cgraph = child W10 graph
Pstate = parent blocker colored state
Cstate = child blocker colored state
```

## 2x2 intervention result

The valid cells are:

```text
Pgraph + Pstate:
  first exit depth = 9
  depth-9 exits    = 2
  depth-10 exits   = 4

Pgraph + Cstate:
  first exit depth = 10
  depth-9 exits    = 0
  depth-10 exits   = 4

Cgraph + Cstate:
  first exit depth = 10
  depth-10 exits   = 5
```

The crossed cell:

```text
Cgraph + Pstate
```

is invalid because the added child edge `5-17` joins two parent-state
vertices of color 3.

Therefore it is not assigned a repair depth.

## State-only sufficiency

The parent graph is unchanged in the comparison

```text
Pgraph + Pstate
        ->
Pgraph + Cstate.
```

Only the blocker colored state is changed.

Nevertheless:

```text
first exit depth: 9 -> 10
depth-9 exits:     2 -> 0
depth-10 exits:    4 -> 4
```

Thus, within this fixed parent topology and repair harness, the child blocker
state is sufficient to reproduce the depth jump.

This is stronger than a correlation between the real W9 and W10 graphs.

## The state change

The parent and child blocker states differ at only two colored vertices:

```text
vertex 4 : 1 -> 0
vertex 17: 3 -> 1
```

The parent topology with this two-vertex child state is proper and satisfies
the Missing-Color invariant.

The same state already produces the merged (0,1) component:

```text
{4,8,9,10,11,12,15,17}
```

seen in the real W10 child.

Therefore the new edge `5-17` is not required at blocker time to create that
component fusion.

## Topology and state play different roles

The explored state-space sizes are:

```text
Pgraph + Pstate = 419838
Pgraph + Cstate = 419841
Cgraph + Cstate = 279935
```

So the state-only intervention changes exit depth without materially changing
the total explored maze size, while the child topology substantially contracts
the maze.

This suggests a useful empirical separation:

```text
blocker state -> shallow-exit availability / first exit depth
topology      -> state-space volume and branching profile
```

This is an observation for this witness, not a general theorem.

## Causal chain supported so far

The current experimental mechanism is:

```text
4-21 -> 5-17
-> earlier repair at step 14 / node 17
-> blocker-state recoloring at vertices 4 and 17
-> (0,1) component fusion on the parent topology itself
-> both depth-nine exits disappear
-> first exit moves from depth 9 to depth 10
```

## What OBS-013 does not establish

It does not establish:

- which of the two color changes, `4:1->0` or `17:3->1`, is individually
  sufficient;
- whether both changes are jointly necessary;
- that the same intervention mechanism generalizes to other witnesses or
  depths;
- that topology never affects exit depth in other cases;
- any Four Color Theorem consequence;
- any Lean theorem.

## Next experiment — partial state intervention

Keep the parent W9 graph fixed and enumerate every subset of the blocker-state
differences.

For the present two differing vertices this gives:

```text
{}        : parent state
{4}       : only vertex 4 changed to child color
{17}      : only vertex 17 changed to child color
{4,17}    : full child blocker state
```

Each state must be checked for properness and the Missing-Color invariant
before its repair depth is interpreted.

The key question is whether the depth jump is already caused by the single
change at vertex 4, or whether the valid two-vertex state change is essential.
