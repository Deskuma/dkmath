# OBS-007 — Stable Depth-Nine Basin under Naive Seeded Objective

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-007 records the first seeded local-search campaign started directly from the
verified depth-nine witness of OBS-006.

The campaign asked whether ordinary resolved-depth optimization could mutate the
known hard map

```text
W9
```

into a depth-ten descendant

```text
W10.
```

It did not.

More importantly, the result diagnosed that the previous resolved objective is
misaligned with this local wall-deepening task.

## Source campaign

Directory:

```text
python/Tromino/results/repair-depth/seeded-w9-d10-v24/
```

Initial witness:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json
seed = 9000035
```

Configuration:

```text
vertices            = 24
jobs                = 64
steps               = 512
warmup_flips        = 0
workers             = 8
max_depth           = 11
target_depth        = 10
node_limit          = 3000000
base_seed           = 10000000
intermediate_policy = endpoint
search_objective    = resolved
stop_on_target      = true
```

## Batch result

All 64 jobs resolved at depth nine:

```text
jobs_completed      = 64
resolved_jobs       = 64
classifications     = {"solved": 64}
mean_resolved_depth = 9
max_resolved_depth  = 9
target_found        = false
stopped_on_target   = false
elapsed_seconds     = 6349.466592788696
```

Thus this bounded local campaign found no W10 descendant.

This is not a proof that no such descendant exists.

## Stable depth-nine basin

Every job began from the same W9 witness and explored legal
solution-preserving flips.

Despite independent random mutation paths, every completed job retained
required depth nine as its best resolved depth.

The recorded best under the old resolved objective is:

```text
job seed             = 10000057
required depth       = 9
repairs              = 4
repair moves total   = 14
mutation suffix      = 12
```

The replay again verifies:

```text
depth 8 = depth_limited
depth 9 = solved
```

so the descendant remains a genuine depth-nine witness.

## Objective drift

The old resolved search objective ranks solved states primarily by:

```text
(required depth, number of repairs, total repair moves)
```

Once every candidate remains at depth nine, the search therefore prefers maps
with more repair events and more total moves.

That is not the quantity needed for W9 -> W10 wall deepening.

The original OBS-006 W9 witness has:

```text
repairs                    = 2
repair moves total         = 10
depth-8 failure expanded   = 202071
critical depth-9 footprint = 15
critical max component     = 9
critical radius            = 2
```

The old-objective best descendant has:

```text
repairs                    = 4
repair moves total         = 14
depth-8 failure expanded   = 194765
critical depth-9 footprint = 14
critical max component     = 8
critical radius            = 2
```

Thus the selected descendant became globally busier while its critical
depth-nine frontier became slightly easier to exhaust:

```text
202071 -> 194765
```

expanded states at depth eight.

This is evidence that total repair count is the wrong local hardness proxy for
the next stage.

## Frontier hardness

For a solved witness of required depth d, define the experimental frontier
quantity

```text
F(G) = expanded states in the replay/evaluation at ceiling d - 1.
```

For the W9 seed:

```text
F(W9) = 202071.
```

The next seeded objective should compare solved maps lexicographically by:

```text
(required depth, frontier expansion)
```

rather than by total repair count.

The intended pressure is:

```text
keep depth 9
-> make the depth-8 frontier harder to exhaust
-> close the remaining depth-9 exit
-> reach depth 10
```

## What OBS-007 establishes

Observed:

- 64/64 seeded jobs remained solved at required depth nine;
- no W10 descendant was found in the bounded 64 x 512 campaign;
- the old resolved objective increased repair count/move count without
  increasing required depth;
- its selected descendant had a smaller depth-8 frontier expansion than the
  original W9 seed;
- the critical repair remained radius two.

Not established:

- that W9 is a strict local maximum;
- that no depth-ten descendant exists near W9;
- that frontier expansion is monotone with true repair depth;
- that larger frontier expansion guarantees a W10 transition;
- any graph-theoretic or Lean theorem.

## Next experiment

Add a dedicated frontier objective and repeat seeded local search from the
original OBS-006 W9 witness.

For solved states, rank primarily by:

```text
required_depth
frontier_expanded_at_depth_minus_one
```

with a mild preference for cleaner witnesses only as a final tie breaker.

The next target remains:

```text
W9 -> W10
```

but the search pressure now acts directly on the critical wall rather than on
the total number of unrelated repairs.
