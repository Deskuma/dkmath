# OBS-009 — Single-Flip Depth Jump Nine to Ten

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-009 freezes the first replay-verified endpoint repair-depth ten witness at
24 vertices and records the local transition from the OBS-008 hard depth-nine
witness.

The transition is exceptionally small: one legal planted-color-preserving
diagonal flip raises the required endpoint repair depth from nine to ten.

## Source campaign

Directory:

```text
python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/
```

Initial witness:

```text
python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json
seed = 11000009
required depth = 9
frontier at depth 8 = 374152
```

Campaign configuration:

```text
vertices            = 24
jobs                = 16
steps               = 384
warmup_flips        = 0
max_depth           = 11
target_depth        = 10
node_limit          = 3000000
base_seed           = 12000000
intermediate_policy = endpoint
search_objective    = frontier
stop_on_target      = true
```

The first completed successful job already reached the target:

```text
jobs_completed      = 1
best seed           = 12000006
best resolved depth = 10
target_found        = true
stopped_on_target   = true
elapsed_seconds     = 1950.0171148777008
```

## Replay-verified depth ten

Replay of seed `12000006` gives:

```text
depth 8  = depth_limited, expanded 264302
depth 9  = depth_limited, expanded 279278
depth 10 = solved
```

At depth ten:

```text
required_depth                 = 10
verified_against_depth_minus_one = true
repairs                        = 4
repair_moves_total             = 14
max_depth_used                 = 10
```

The critical repair remains at node `19`, restore step `16`.

Its geometry is:

```text
repair depth              = 10
component sizes           = 8,1,2,1,1,1,4,2,2,1
max component size        = 8
footprint size            = 15
distance from blocker     = 1..2
```

Thus the depth-ten repair still fits inside graph radius two of the blocked
node.

The precise harness-relative statement is:

```text
D_endpoint^H(G_12000006) = 10
```

where `H` fixes the current restore order, direct-choice rule, locked frame,
Kempe-component move family, endpoint admissibility, and BFS repair search.

## Single-flip transition

The W10 witness has:

```text
initial_flip_history_length = 1744
mutation_suffix_length      = 1
steps_done                  = 4
accepted_mutations          = 1
```

The only accepted mutation beyond the OBS-008 seed is:

```text
[4,21,5,17]
```

It replaces the diagonal `4-21` by `5-17` in the quadrilateral on
`{4,5,17,21}`.

Face change:

```text
remove {4,5,21}
remove {4,17,21}

add    {4,5,17}
add    {5,17,21}
```

This one local diagonal flip changes the required depth:

```text
9 -> 10
```

under the present harness.

## Three-step local path from the original W9

Combining OBS-008 and OBS-009, the original OBS-006 W9 graph differs from the
new W10 graph by three net local diagonal flips.

The graph-level symmetric difference is six removed/added triangle pairs:

```text
removed:
  {4,5,14}
  {4,5,21}
  {4,14,19}
  {4,17,21}
  {5,6,21}
  {5,6,22}

added:
  {4,5,17}
  {4,5,19}
  {5,14,19}
  {5,17,21}
  {5,21,22}
  {6,21,22}
```

The important experimental chain is therefore:

```text
W9(original)
  -- two net flips --> W9(frontier-amplified)
  -- one flip      --> W10
```

## Interpretation

The frontier objective did not merely find a larger search count.

It first moved within the depth-nine basin to a harder frontier and then, from
that state, one further local mutation crossed the discrete depth boundary.

This suggests a local wall-deepening picture:

```text
frontier amplification
-> critical local mutation
-> next repair-depth level
```

This remains an algorithm-relative observation.

## What OBS-009 does not establish

It does not establish:

- that the flip `4-21 -> 5-17` is the unique one-flip route from this W9;
- that every sufficiently hard frontier has a depth-raising adjacent flip;
- that repair depth is unbounded at 24 vertices;
- that radius two suffices for arbitrary depth;
- a graph-theoretic Four Color Theorem result;
- any Lean theorem.

## Next experiment

Enumerate **every** legal planted-color-preserving one-flip neighbor of the
OBS-008 W9 frontier witness and classify each neighbor.

The next questions are:

```text
How many one-flip neighbors remain at depth 9?
How many drop below depth 9?
How many reach depth 10?
Is [4,21,5,17] unique among depth-raising flips?
```

This converts the accidental-looking transition into a complete local
neighborhood measurement.
