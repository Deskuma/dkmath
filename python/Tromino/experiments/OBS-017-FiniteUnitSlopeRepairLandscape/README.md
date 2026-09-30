# OBS-017 — Finite Unit-Slope Repair Landscape

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-017 freezes the complete admissible blocker-state component scan for the W9
witness at node 19 / restore step 16.

The admissible state graph keeps the parent W9 topology fixed and allows only
single-vertex recolorings of unlocked colored blocker neighbors that preserve:

```text
proper coloring
and
Missing-Color invariant
```

Repair first-exit depth is then evaluated at every state.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-state-component-v24/
```

Primary file:

```text
summary.json
```

The component scan completed without truncation.

## Complete finite component

The admissible component contains:

```text
states = 32
edges  = 48
degree min  = 1
degree max  = 5
degree mean = 3
```

The graph is connected by construction.

Its cycle rank is:

```text
48 - 32 + 1 = 17
```

so this is not a tree-like local neighborhood.

A direct graph check also shows that this 32-state component is bipartite.

## Repair-depth distribution

Let

```text
h(S) = first repair exit depth at blocker state S.
```

Across all 32 states:

```text
h = 8 :  9 states
h = 9 : 19 states
h = 10:  4 states
```

No state has first exit below 8 or above 10 within this complete component.

The original W9 blocker state is state 22 with:

```text
h(22) = 9
```

and its three one-step neighbors have depths:

```text
10, 8, 8
```

so the original state is a genuine saddle in the complete admissible component.

## Unit-slope observation

For all 48 admissible one-point recoloring edges:

```text
|h(S') - h(S)| <= 1
```

The edge counts are:

```text
delta  0 : 19 edges
|delta| 1 : 29 edges
```

There are no admissible edges with a repair-depth jump of magnitude two.

This is the first complete finite witness for a unit-slope repair-depth
landscape.

It is still an empirical finite observation, not a general theorem.

## Peaks, plateaus, valleys, and saddles

The four depth-ten states are:

```text
0, 12, 13, 25
```

States 12 and 13 form a depth-ten plateau.

States 0 and 25 are isolated depth-ten peaks whose adjacent states all have
depth nine.

The nine depth-eight states form several disconnected depth-eight plateaus or
singletons inside the full graph.

Depth-nine states form the dominant middle layer and include both saddles and
flat transitions.

Thus the landscape is not a monotone chain.

It has:

```text
peaks
plateaus
saddles
valleys
cycles
```

## Missing-color chamber

The mutable blocker-neighbor states reachable inside this component never use
color 2.

At the original blocker state all remaining vertices 19..23 see the same
colored-neighbor palette:

```text
{0,1,3}
```

so color 2 is the common missing future color.

The full 32-state component confirms that, under the chosen admissible
one-point dynamics, color 2 remains outside the reachable chamber.

## Interpretation

The current finite mechanism can be summarized as:

```text
Missing-Color constraint
-> finite admissible state chamber
-> reversible one-point state moves
-> repair-depth height h
-> local edge slope in {-1,0,+1}
```

This is closer to a finite height landscape than to a deterministic Collatz
map: the transition graph branches and contains cycles, while the scalar
observable h varies locally.

## What OBS-017 does not establish

It does not establish:

- that every witness has a finite component of the same form;
- that every admissible edge in every witness satisfies |delta h| <= 1;
- that repair depth is a discrete Morse function;
- that the height range is always three consecutive integers;
- that the missing-color chamber is globally invariant across graph changes;
- any Four Color Theorem consequence;
- any general Lean theorem.

## Next experiment

Repeat the same complete component scan on the actual W10 child witness.

Use a repair ceiling of 11 so a possible depth-eleven state is visible.

A static admissibility probe of the W10 blocker state already gives:

```text
admissible states = 4
edges             = 3
degree range      = 1..2
```

and the state graph is a simple four-state path.

This is an excellent independent contrast with the cyclic 32-state W9 chamber.

The key questions are:

```text
Does W10 contain a depth-11 state?
Does every W10 edge also satisfy |delta h| <= 1?
Does the much smaller admissible chamber preserve the same height law?
```
