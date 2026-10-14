# OBS-006 — Radius-Two Endpoint Repair Depth Nine

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-006 freezes the first replay-verified endpoint repair-depth nine witness at
24 vertices, together with the first geometry instrumentation for the critical
composite repair.

The main question after OBS-005 was whether greater repair depth necessarily
forces the solver to reach farther away from the blocked node.

The present witness says: not yet.

A depth-nine repair is realized while the entire repair footprint remains
within graph distance two of the blocked node.

## Source campaign

Directory:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/
```

Configuration:

```text
vertices            = 24
jobs requested      = 2000
steps               = 3000
warmup_flips        = 64
workers             = 8
max_depth           = 10
target_depth        = 9
node_limit          = 1500000
base_seed           = 9000000
intermediate_policy = endpoint
search_objective    = resolved
stop_on_target      = true
```

The target was found after 72 completed jobs and the run stopped on target.

Frozen batch summary:

```text
jobs_completed      = 72
resolved_jobs       = 72
classifications     = {"solved": 72}
max_resolved_depth  = 9
mean_resolved_depth = 5.833333333333333
best_resolved_seed  = 9000035
target_found        = true
stopped_on_target   = true
elapsed_seconds     = 7656.416496515274
```

The mean depth is not interpreted as a natural-frequency statistic because the
search objective actively selects for deeper solved witnesses.

## Verified depth-nine witness

Files:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json
python/Tromino/results/repair-depth/endpoint-d9-v24/replay-best-resolved.json
```

Seed:

```text
9000035
```

Replay frontier:

| depth ceiling | result | expanded states at blocker |
| ---: | --- | ---: |
| 0 | forced repair | — |
| 1 | depth limited | 20 |
| 2 | depth limited | 229 |
| 3 | depth limited | 1690 |
| 4 | depth limited | 8951 |
| 5 | depth limited | 34345 |
| 6 | depth limited | 91988 |
| 7 | depth limited | 164226 |
| 8 | depth limited | 202071 |
| 9 | solved | 202085 |

The critical repair occurs at:

```text
restore step = 16
node         = 19
```

The full solved lift has two repair events:

```text
node 18, step 15: repair depth 1
node 19, step 16: repair depth 9
```

and therefore:

```text
repairs                        = 2
repair_moves_total             = 10
required_depth                 = 9
verified_against_depth_minus_one = true
```

Thus the replay-verified experimental frontier is:

```text
D_endpoint(24) >= 9
```

for the present planted generator, deterministic restore order, locked frame,
direct-choice rule, and Kempe-component exchange proxy.

## Critical depth-nine repair

The depth-nine component sizes are:

```text
9, 1, 2, 1, 1, 1, 3, 2, 2
```

with geometry:

```text
max_component_size         = 9
footprint_size             = 15
min_distance_from_current  = 1
max_distance_from_current  = 2
```

The repair footprint is:

```text
{3,4,5,6,7,8,9,10,11,12,13,14,15,17,18}
```

The successful exchange sequence is:

```text
(0 <-> 1) on {4,5,6,8,9,10,11,12,15}
(0 <-> 1) on {13}
(0 <-> 2) on {3,8}
(0 <-> 2) on {4}
(0 <-> 2) on {6}
(0 <-> 2) on {9}
(2 <-> 3) on {4,14,17}
(2 <-> 3) on {8,18}
(0 <-> 3) on {7,10}
```

After the ninth primitive exchange, node `19` is assigned color `0`.

## Structural interpretation

OBS-005 gave a pure depth-eight repair whose primitive components were all
small.

OBS-006 raises the depth to nine and now permits a larger component and larger
union footprint, but the graph radius of the entire repair remains only two.

Therefore the current data support separating at least three quantities:

```text
repair depth
repair footprint size
repair radius
```

The depth-nine witness shows that deeper exchange composition need not yet imply
greater graph radius.

A useful working picture is:

```text
small-radius neighborhood
    +
many interacting exchange choices
    =
deep local maze
```

This is still an algorithm-relative observation, not a graph-theoretic theorem.

## What OBS-006 does not establish

It does not establish:

- that radius two suffices for arbitrary endpoint repair depth;
- that repair depth is unbounded at 24 vertices;
- that the depth-nine witness is minimal over all restore orders;
- that footprint size must grow with depth;
- that the present Kempe-component proxy is the final DkMath GapSwap;
- any Four Color Theorem result;
- any asymptotic complexity result;
- any quantum-advantage result;
- any Lean theorem.

## Next experiment

The next search should no longer restart every job from a fresh random planted
instance.

Instead use the verified depth-nine witness itself as the initial state and
search its legal flip neighborhood for a depth-ten descendant:

```text
W_9 -> W_9' -> W_9'' -> ... -> W_10 ?
```

This changes the experimental question from:

```text
Can a random planted map happen to contain a depth-ten maze?
```

to:

```text
Can one deepen an already-known depth-nine wall by local
solution-preserving mutations?
```

If successful, the mutation history between the seed witness and its first
depth-ten descendant becomes candidate data for a recursive wall gadget.
