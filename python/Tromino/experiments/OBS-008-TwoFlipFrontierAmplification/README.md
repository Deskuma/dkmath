# OBS-008 — Two-Flip Frontier Amplification

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-008 records the first successful use of the frontier search objective on the
verified depth-nine witness from OBS-006.

The target depth ten was not reached, but the critical depth-eight frontier was
made substantially harder while required depth remained nine.

The key structural feature is that the final hard descendant differs from the
seed by only two net diagonal flips.

## Source campaign

Directory:

```text
python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/
```

Initial witness:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json
seed = 9000035
```

Configuration:

```text
vertices            = 24
jobs                = 32
steps               = 512
warmup_flips        = 0
workers             = 8
max_depth           = 11
target_depth        = 10
node_limit          = 3000000
base_seed           = 11000000
intermediate_policy = endpoint
search_objective    = frontier
stop_on_target      = true
```

## Campaign result

All 32 jobs remained solved at required depth nine:

```text
jobs_completed      = 32
resolved_jobs       = 32
mean_resolved_depth = 9
max_resolved_depth  = 9
target_found        = false
stopped_on_target   = false
elapsed_seconds     = 4239.287391901016
```

No W10 descendant was found in this bounded campaign.

## Frontier amplification

The OBS-006 seed has:

```text
required depth      = 9
depth-8 expanded    = 202071
critical footprint  = 15
max component size  = 9
critical radius     = 2
```

The best frontier descendant is seed `11000009`:

```text
required depth      = 9
depth-8 expanded    = 374152
critical footprint  = 13
max component size  = 6
critical radius     = 2
repair moves total  = 11
repairs             = 2
mutation suffix     = 4
```

Replay verifies:

```text
depth 8 = depth_limited, expanded 374152
depth 9 = solved
```

Thus the frontier increase is:

```text
202071 -> 374152
delta = 172081
```

while the repair remains at graph radius two.

This supports the intended interpretation of the frontier objective: it can make
the critical wall significantly harder without merely increasing the number of
unrelated repairs.

## Net mutation from W9

The recorded suffix after the OBS-006 seed is:

```text
[4,21,5,17]
[5,17,4,21]
[4,14,5,19]
[5,6,22,21]
```

The first two flips reverse one another. Therefore the final graph differs from
the seed by two net diagonal flips.

The corresponding face changes are:

```text
remove {4,5,14}, {4,14,19}
add    {4,5,19}, {5,14,19}

remove {5,6,21}, {5,6,22}
add    {5,21,22}, {6,21,22}
```

This gives a concrete local wall mutation that nearly doubles the measured
depth-eight frontier while preserving required depth nine.

## Structural interpretation

The new data separate three notions even more clearly:

```text
required repair depth
frontier search hardness
geometric footprint/radius
```

From OBS-006 to OBS-008:

```text
required depth:       9 -> 9
frontier expanded:    202071 -> 374152
footprint size:       15 -> 13
max component size:   9 -> 6
radius:                2 -> 2
```

So a much harder frontier does not require a larger spatial footprint in this
example.

The observed increase is algorithm-relative and does not establish a universal
complexity lower bound.

## What OBS-008 does not establish

It does not establish:

- a depth-ten witness;
- monotonicity of frontier expansion under local flips;
- that the two net flips are uniquely responsible for the increase;
- that frontier expansion is a theorem-level invariant;
- that radius two suffices at arbitrary repair depth;
- any Four Color Theorem consequence;
- any Lean theorem.

## Next experiment

Use the best frontier witness itself as the next initial state and continue
frontier ascent:

```text
W9^(0) --frontier--> W9^(1) --frontier--> ... --?--> W10
```

The new baseline is:

```text
F(W9^(1)) = 374152.
```

A useful next result is either:

1. a replay-verified W10 descendant, or
2. a second verified frontier amplification above 374152.

The mutation suffix between successive frontier maxima should continue to be
recorded because repeated small local mutations may expose a reusable wall
deepening gadget.
