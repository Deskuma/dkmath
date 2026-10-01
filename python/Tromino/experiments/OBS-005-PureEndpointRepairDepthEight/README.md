# OBS-005 — Pure Endpoint Repair Depth Eight

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-005 freezes a replay-verified endpoint repair-depth eight witness at the
same fixed graph size used by OBS-004.

The key feature is that the witness requires exactly one repair event, and that
single repair event has primitive-exchange depth eight.

This makes the example cleaner than a run whose maximum depth is eight only
because several unrelated repair events occur during the lift.

## Source campaign

Directory:

```text
python/Tromino/results/repair-depth/endpoint-d8-v24/
```

Campaign configuration:

```text
vertices            = 24
jobs requested      = 3000
steps               = 3000
warmup_flips        = 64
max_depth           = 10
target_depth        = 8
node_limit          = 1500000
base_seed           = 8000000
intermediate_policy = endpoint
search_objective    = resolved
```

The run was intentionally stopped early after the target had already been
found. The frozen summary contains 47 completed jobs, all solved, with maximum
resolved depth eight.

The batch frequency is not interpreted as a distribution over planar maps.

## Pure depth-eight witness

Files:

```text
python/Tromino/results/repair-depth/endpoint-d8-v24/witness-8000005.json
python/Tromino/results/repair-depth/endpoint-d8-v24/replay-8000005.json
```

Seed:

```text
8000005
```

The replay frontier is:

| depth ceiling | result | expanded states |
| ---: | --- | ---: |
| 0 | forced repair | — |
| 1 | depth limited | 20 |
| 2 | depth limited | 213 |
| 3 | depth limited | 1378 |
| 4 | depth limited | 6203 |
| 5 | depth limited | 20454 |
| 6 | depth limited | 50809 |
| 7 | depth limited | 97056 |
| 8 | solved | 119630 |

The critical repair occurs at:

```text
restore step = 17
node         = 20
```

and the successful endpoint run records:

```text
repairs                        = 1
repair_moves_total             = 8
max_depth_used                 = 8
required_depth                 = 8
verified_against_depth_minus_one = true
assigned_color                 = 0
```

Therefore the current experimental frontier is:

```text
D_endpoint(24) >= 8
```

for the present planted generator, deterministic restore order, locked frame,
direct-choice rule, and Kempe-component exchange proxy.

## Primitive exchange sequence

The single depth-eight repair is:

```text
(0 <-> 1) on {4, 15}
(0 <-> 2) on {11}
(0 <-> 2) on {12}
(0 <-> 3) on {3, 4}
(0 <-> 3) on {5, 14}
(0 <-> 3) on {18}
(1 <-> 2) on {10, 12, 13, 16}
(2 <-> 3) on {8, 13, 16, 17}
```

The component sizes are:

```text
2, 1, 1, 2, 2, 1, 4, 4
```

so the deepest known repair is not caused by a single very large component.
It is produced by composing several small component exchanges.

This motivates separating:

```text
repair depth
component size
repair footprint
repair radius
```

instead of treating depth as a proxy for geometric locality.

## Interpretation

OBS-004 showed that endpoint repair can require depth seven.

OBS-005 strengthens this at the same fixed vertex count and with a particularly
clean witness:

```text
one obstruction
-> one repair event
-> eight primitive exchanges
-> repaired endpoint
```

Thus the observed depth increase from seven to eight does not require enlarging
the map from 24 vertices.

This supports the working interpretation that maze depth depends on the
interaction pattern of walls, not only on graph size.

## What OBS-005 does not establish

It does not establish:

- an unbounded repair-depth theorem;
- that depth eight is minimal over all restore orders;
- that the Kempe-component proxy is the final DkMath GapSwap primitive;
- that small component size implies geometric locality;
- a bound or asymptotic law for repair footprint or radius;
- any Four Color Theorem consequence;
- any quantum-advantage statement;
- any Lean theorem.

## Next experiment

Continue at 24 vertices and search for endpoint depth nine, but instrument the
geometry of each successful composite repair.

For every traced repair record at least:

```text
component_sizes
max_component_size
footprint_vertices
footprint_size
min_distance_from_current
max_distance_from_current
```

The next harness should also support `--stop-on-target` so a target witness
does not leave thousands of already-unnecessary jobs running.

The next question is therefore not only:

```text
Can D_endpoint(24) reach 9?
```

but also:

```text
Does increasing repair depth require a growing spatial footprint,
or can arbitrarily deep exchange compositions remain geometrically local?
```
