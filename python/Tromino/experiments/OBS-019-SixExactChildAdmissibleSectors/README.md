# OBS-019 — Six Exact Child-Admissible Sectors

Date: 2026-09-30

Corrected census source:
`python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/summary.json`

## Aggregate

```text
legal preserving neighbors           = 17
child projection subsets of W9       = 6
induced W9 subgraph matches           = 6
exact child-admissible sector matches = 6
simple added-edge predictor matches   = 5
blocker adjacency changed             = 7
```

Exact sector neighbors:

```text
1  [4,21,5,17]    child states 4
3  [5,22,21,14]   child states 32
11 [15,22,6,11]   child states 32
13 [17,21,15,4]   child states 8
14 [19,22,13,18]  child states 6
16 [21,22,6,5]    child states 16
```

The six cases satisfy all three:

```text
child projections are a subset of the W9 state set;
child edges equal the induced W9 edges on that subset;
the child chamber equals the connected component selected by the full
child-admissibility predicate and containing the child baseline.
```

Neighbor 16 is the important correction to the simpler story. The added edge
alone does not predict its 16-state child sector. The full child context does:
child graph, fixed restore-prefix colors, and Missing-Color invariant.

Therefore the useful abstraction is:

```text
full child admissibility
-> restriction of parent states
-> connected component containing child baseline
```

rather than `added edge alone -> sector`.

For this witness the 17 one-flip neighbors split into 6 transport-compatible
restriction cases and 11 state-regenerating cases.

## Lean status

A generic finite-graph sectorization lemma is now a plausible Lean target:
under shared mutable coordinates, child-admissible inclusion into the parent
state set, and the same one-coordinate transition relation, the child chamber
is the connected component of the parent graph induced by child-admissible
states.

The repair-depth unit-slope law remains empirical and should not yet be
promoted to a general theorem.

## Next

Evaluate repair first-exit depth on every state of the six exact sectors and
compare child heights against their matched W9 heights. Check height
preservation, edge `|delta h|`, depth 11, and repair-maze volume.
