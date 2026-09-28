# OBS-004 — Endpoint Repair Depth Seven

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-004 records the first long-run campaign in which endpoint Missing-Color
restoration is the primary repair policy and the search objective explicitly
maximizes verified **resolved** repair depth.

The question is:

> If primitive exchanges may temporarily lose the Missing Color, how deep can a
> composite local repair still become before a valid endpoint is recovered?

This experiment follows OBS-003, which showed that strict intermediate
Missing-Color preservation can exclude repair paths that become available when
only the start and end states are required to be safe.

## Source run

Directory:

```text
python/Tromino/results/repair-depth/endpoint-d6-v24/
```

Configuration:

```text
vertices            = 24
jobs                = 2000
steps               = 2000
warmup_flips        = 48
workers             = 8
max_depth           = 8
target_depth        = 6
node_limit          = 750000
base_seed           = 7000000
intermediate_policy = endpoint
search_objective    = resolved
```

The search keeps a planted proper four-coloring as a hidden witness of
solvability. The solver is not given that coloring.

## Batch result

The frozen summary is:

```text
jobs_completed      = 2000
resolved_jobs       = 2000
classifications     = {"solved": 2000}
max_resolved_depth  = 7
mean_resolved_depth = 5.218
best_resolved_seed  = 7001217
target_found        = true
elapsed_seconds     = 8228.199981689453
```

The mean depth is **not** a natural-frequency statistic. The adversarial search
objective intentionally prefers deeper solved witnesses.

The structurally important observations are:

- every completed job produced a resolved witness under the configured endpoint
  policy and ceiling;
- no unresolved frontier was recorded in this campaign;
- a replay-verified endpoint depth-seven witness was found.

## Verified endpoint depth-seven witness

Files:

```text
python/Tromino/results/repair-depth/endpoint-d6-v24/best_resolved_witness.json
python/Tromino/results/repair-depth/endpoint-d6-v24/replay-best-resolved.json
```

Seed:

```text
7001217
```

Replay frontier:

| depth ceiling | result |
| ---: | --- |
| 0 | forced repair |
| 1 | depth limited |
| 2 | depth limited |
| 3 | depth limited |
| 4 | depth limited |
| 5 | depth limited |
| 6 | depth limited |
| 7 | solved |

The critical obstruction occurs at restore step `18`, node `21`.

At depth six:

```text
classification  = depth_limited
expanded        = 20605
hit_depth_limit = true
repairs_so_far  = 5
```

At depth seven the repair succeeds:

```text
required_depth             = 7
verified_against_depth_minus_one = true
repair_depth_at_node_21    = 7
repair_search_expanded     = 25363
repairs_total              = 6
repair_moves_total         = 14
assigned_color             = 1
```

The successful seven-move composite repair is:

```text
(0 <-> 1) on {12}
(0 <-> 1) on {16}
(0 <-> 3) on {3}
(0 <-> 3) on {14}
(0 <-> 1) on {7, 9, 14, 20}
(0 <-> 3) on {18}
(2 <-> 3) on {4, 11, 17}
```

After these seven primitive exchanges, node `21` receives color `1`.

Thus, for the current generator, restore order, locked frame, and
Kempe-component exchange proxy,

```text
D_endpoint(24) >= 7
```

is a replay-verified experimental observation.

## Structural interpretation

OBS-003 showed that strict intermediate Gap preservation can create artificial
unreachability.

OBS-004 shows that removing that restriction does **not** collapse every repair
to shallow depth.

The distinction is therefore:

```text
strict repair:
    intermediate states must remain Safe

endpoint repair:
    intermediate states may leave Safe
    only the repair start and endpoint must be Safe
```

and yet endpoint repair can still require a seven-step composite exchange.

This supports the existence of a genuine local maze-depth phenomenon within the
present experimental move system.

A useful working observable is:

```text
D_endpoint(G)
  = minimum primitive-exchange depth needed by the current deterministic lift
    to recover a valid endpoint at its deepest repair event.
```

This definition remains algorithm-relative: it depends on the restore order,
locked frame, direct-choice rule, and primitive move family.

## What OBS-004 establishes only as observation

Recorded:

- endpoint repair does not eliminate deep composite repairs;
- a verified endpoint repair-depth seven witness exists at 24 vertices;
- depth six fails for that witness while depth seven succeeds;
- all 2000 jobs in this campaign resolved under the configured depth ceiling
  eight.

Not established:

- that every 24-vertex planted instance resolves by depth eight;
- that endpoint repair is universally complete;
- that repair depth is unbounded in graph size;
- that depth seven is minimal over all restore orders or move families;
- that Kempe-component exchange is the final DkMath GapSwap primitive;
- any Four Color Theorem result;
- any asymptotic complexity or quantum-advantage claim;
- any Lean theorem.

## Next experiment

Keep the vertex count fixed at 24 and search first for a verified endpoint
repair-depth eight witness.

This is intentional: before increasing graph size, test whether greater maze
depth can be produced by rearranging walls inside the same-size state space.

Suggested campaign:

```text
vertices            = 24
jobs                = 3000
steps               = 3000
warmup_flips        = 64
max_depth           = 10
target_depth        = 8
node_limit          = 1500000
base_seed           = 8000000
intermediate_policy = endpoint
search_objective    = resolved
```

If depth eight or greater is replay-verified at 24 vertices, continue at fixed
size before enlarging the map. If the frontier remains at seven after a
substantially larger search, then compare against 28- and 32-vertex campaigns
to begin measuring size dependence.
