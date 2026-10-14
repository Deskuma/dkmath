# OBS-020 — Unit-Slope Is Structural; Cross-Topology Height Preservation Is Not

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Source

```text
python/Tromino/results/repair-depth/w9-sector-height-census-v24/
```

The census evaluates all states of the six exact transport-compatible child
sectors found in OBS-019.

## Aggregate result

```text
neighbors evaluated = 6
states evaluated    = 98

height labels equal to matched W9 state = 21
height labels lower than matched W9     = 77
height labels higher than matched W9    = 0

depth 11 found = none
```

Only neighbor 1 preserves every W9 height label.

Observed child-minus-parent height shifts over all 98 states:

```text
 0 : 21 states
-1 : 32 states
-2 : 29 states
-3 :  8 states
-4 :  8 states
```

Cross-topology height preservation is therefore false as a general rule for
this one-flip census.

## Per-neighbor child height ranges

```text
neighbor  1 : 4 states   heights 9..10   all labels preserved
neighbor  3 : 32 states  heights 6..8
neighbor 11 : 32 states  heights 5..8
neighbor 13 : 8 states   heights 7..9
neighbor 14 : 6 states   heights 4..5
neighbor 16 : 16 states  heights 8..9
```

No child state exceeds the matched W9 height in this census. This monotonic
direction is empirical only.

## Unit-slope survives every tested topology

Every one of the six child chambers satisfies:

```text
|h(S') - h(S)| <= 1
```

on every admissible one-point recoloring edge.

## One-point recoloring edges are singleton Kempe exchanges

Every edge in the six child state graphs was checked directly.

For all state-graph edges:

```text
the two endpoint colorings differ at exactly one unlocked vertex v;
the old/new two-color Kempe component containing v is exactly {v}.
```

There were no exceptions.

Properness explains this: the source coloring gives no adjacent vertex with the
old color, the target coloring gives no adjacent vertex with the new color, so
v is isolated in the old/new two-color induced subgraph. Because v is
unlocked, swapping that singleton component is a legal Kempe exchange.

Hence every admissible one-point recoloring edge is also one edge of the repair
move graph.

## Repair height as distance to the exit set

For all 98 evaluated roots, the initial safe-candidate set is empty.

Therefore the reported first-exit depth is the shortest number of Kempe
exchange moves from the root state to a state having a safe candidate.

For a fixed topology, remaining set, blocker, and policy, define:

```text
Exit = states with a safe candidate
h(S) = graph distance from S to Exit
```

on the Kempe exchange graph.

Distance to a fixed target set on an undirected graph is 1-Lipschitz across an
edge. Since Kempe exchange is involutive, the repair graph is undirected.

Thus for adjacent repair states S,T:

```text
h(S) <= h(T) + 1
h(T) <= h(S) + 1
```

and therefore:

```text
|h(S) - h(T)| <= 1
```

This is now a general theorem candidate, not merely an empirical pattern.

## Formalization boundary

Ready for Lean:

```text
1. child-admissibility restriction -> connected sector decomposition;
2. repair height = distance to an exit set;
3. distance-to-exit is unit-slope along exchange edges;
4. proper one-point recoloring -> singleton Kempe exchange.
```

Still empirical:

```text
child repair height <= matched parent repair height;
specific height distributions such as {8,9,10};
whether preserving flips always admit a useful transport;
any Four Color Theorem conclusion.
```

## Next step

Move the structural layer into Lean before running more large searches.

The experimental harness should remain as a source of counterexamples and
calibration witnesses, but the unit-slope law no longer needs additional
statistical support once its graph-distance formulation is kernel checked.
