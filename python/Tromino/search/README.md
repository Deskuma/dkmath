# Repair-depth long-run search

This directory contains the long-running search harness for the Tromino Missing-Color / maze-depth experiment.

The current goal is narrower than four-coloring itself: starting from a known tetrahedral / four-state solution and adding solution-preserving combinatorial walls, how large can the local repair depth become before the solver can continue its lift?

The search keeps a planted proper four-coloring as a hidden witness of solvability. The solver is not given that coloring.

## Generator

The base structure has an implicit outer sea of color 0, a fixed outer triangle colored 1,2,3, and one initial interior vertex of color 0.

An internal triangular face is refined by inserting one vertex. Because the three face vertices have three distinct colors, the inserted vertex receives the unique missing fourth color in the planted solution. Pure face refinement therefore increases resolution while retaining an explicit solution lineage.

Complexity is then added with legal diagonal edge flips. A flip is accepted by the generator only when the new diagonal also respects the planted coloring.

    resolution growth   = face subdivision
    maze-wall insertion = solution-preserving edge flip
    solver difficulty   = required local repair depth

## Solver

The solver restores vertices in refinement birth order. For each not-yet-restored vertex v it tracks P(v), the colors already visible on the restored boundary of v, and attempts to maintain the Missing-Color Invariant |P(v)| <= 3.

If a direct color keeps the invariant, no exchange is performed. If every direct color would violate the invariant, the solver searches two-color Kempe-component exchanges as the current diagnostic proxy for GapSwap. The outer frame is locked.

Two repair policies are available. strict requires every intermediate exchange state to preserve the invariant. endpoint allows intermediate exchange states to violate it, but a repaired endpoint must restore the invariant before the current vertex is colored. The proxy exchange must not be confused with the eventual DkMath Tromino GapSwap definition.

## Quick smoke test

From the repository root:

    python3 python/Tromino/search/repair_depth_search.py search \\
      --vertices 12 \\
      --jobs 8 \\
      --steps 100 \\
      --workers 2 \\
      --max-depth 4 \\
      --target-depth 3 \\
      --output /tmp/tromino-depth-smoke

## Suggested first long run

    mkdir -p python/Tromino/results/repair-depth/d5-v24

    python3 python/Tromino/search/repair_depth_search.py search \\
      --vertices 24 \\
      --jobs 2000 \\
      --steps 2000 \\
      --warmup-flips 48 \\
      --workers "$(nproc)" \\
      --max-depth 6 \\
      --target-depth 5 \\
      --node-limit 500000 \\
      --base-seed 6000000 \\
      --intermediate-policy strict \\
      --output python/Tromino/results/repair-depth/d5-v24

The process checkpoints after each completed independent job, so an interrupted run can be resumed by running the same command again. Seeds already present in runs.jsonl are skipped.

If this run spends excessive time in repair BFS, reduce --workers before reducing the node limit. Each worker maintains its own repair frontier and can therefore consume substantial memory.

## Output

A run directory contains:

    config.json
    runs.jsonl
    summary.json
    best_witness.json

runs.jsonl is crash-safe raw job output and can become large. best_witness.json contains the final triangular faces, planted colors, refinement birth order, complete flip history, solver classification, and trace metadata required to reconstruct the hard instance.

## Replay a witness

    python3 python/Tromino/search/repair_depth_search.py replay \\
      python/Tromino/results/repair-depth/d5-v24/best_witness.json \\
      --min-depth 0 \\
      --max-depth 10 \\
      --node-limit 2000000 \\
      --intermediate-policy strict \\
      --trace \\
      --stop-on-success \\
      --output python/Tromino/results/repair-depth/d5-v24/replay-strict.json

If strict replay remains unresolved, also replay with --intermediate-policy endpoint. This comparison helps distinguish a genuinely deeper maze from a route that exists only when the strict intermediate Missing-Color condition is relaxed.

## Result return policy

For chat-side analysis, the smallest useful return is summary.json plus best_witness.json, and replay-strict.json when relevant. These files can be attached directly in chat.

For repository-side preservation, commit the small result files into a named result directory. Raw runs.jsonl is ignored by default because long runs can be large; add it explicitly only when the complete raw record is useful.

## Current target

The immediate target is a verified depth-5 witness. More importantly, classify the first hard examples as one of three cases: genuinely solved only after depth 5 or greater, merely depth-limited by the configured ceiling, or blocked by the strict Missing-Color invariant even though the planted coloring proves that a global proper coloring exists.

The third case is especially valuable because it means the present invariant or proxy move set is too restrictive rather than merely revealing a deeper maze.


## Endpoint-depth campaign after OBS-003

OBS-003 showed that a witness exhausted under strict intermediate
Missing-Color preservation can be solved when only the repair endpoint is
required to restore the invariant.

The next campaign therefore makes endpoint repair the primary policy and asks
for the largest **verified solved** repair depth rather than allowing unresolved
states to dominate the search objective.

Recommended first run:

    mkdir -p python/Tromino/results/repair-depth/endpoint-d6-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 2000 \
      --steps 2000 \
      --warmup-flips 48 \
      --workers "$(nproc)" \
      --max-depth 8 \
      --target-depth 6 \
      --node-limit 750000 \
      --base-seed 7000000 \
      --intermediate-policy endpoint \
      --search-objective resolved \
      --output python/Tromino/results/repair-depth/endpoint-d6-v24

The search now maintains separate frontier files:

    best_witness.json
    best_resolved_witness.json
    best_unresolved_witness.json

For this campaign, the primary record is best_resolved_witness.json.

best_unresolved_witness.json remains diagnostically useful, but unresolved
states no longer outrank resolved states in --search-objective resolved mode.

The summary records both frontiers independently.

If the endpoint run reaches verified depth 6 quickly, rerun with a fresh
output directory and target depth 7 before increasing the vertex count. If
depth 6 is not found, keep n=24 and increase jobs/steps first; this helps
separate insufficient search effort from size-dependent difficulty.

After the run, replay the best resolved witness from depth 0 upward:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/endpoint-d6-v24/best_resolved_witness.json \
      --min-depth 0 \
      --max-depth 10 \
      --node-limit 3000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/endpoint-d6-v24/replay-best-resolved.json

The next observation should be recorded only after this replay confirms the
depth-minus-one failure and the successful endpoint depth.


## Fixed-size endpoint depth-8 campaign after OBS-004

OBS-004 established a replay-verified endpoint depth-seven witness at 24
vertices. The next test keeps the graph size fixed and increases search effort
before changing `n`.

Recommended run:

    mkdir -p python/Tromino/results/repair-depth/endpoint-d8-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 3000 \
      --steps 3000 \
      --warmup-flips 64 \
      --workers "$(nproc)" \
      --max-depth 10 \
      --target-depth 8 \
      --node-limit 1500000 \
      --base-seed 8000000 \
      --intermediate-policy endpoint \
      --search-objective resolved \
      --output python/Tromino/results/repair-depth/endpoint-d8-v24

The primary output is again:

    best_resolved_witness.json

After completion, replay it with a larger ceiling:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/endpoint-d8-v24/best_resolved_witness.json \
      --min-depth 0 \
      --max-depth 12 \
      --node-limit 5000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/endpoint-d8-v24/replay-best-resolved.json

A new observation should be frozen only after replay confirms failure at
`d-1` and success at `d`.


## Endpoint depth-9 + repair-geometry campaign after OBS-005

OBS-005 fixed a pure endpoint repair-depth eight witness at 24 vertices.
The next campaign keeps the same vertex count and asks whether the wall
interaction can be deepened again.

The harness now adds repair-geometry fields to every traced repair:

    component_sizes
    max_component_size
    footprint_vertices
    footprint_size
    min_distance_from_current
    max_distance_from_current

These fields distinguish exchange depth from spatial extent.

The search also accepts `--stop-on-target`. Once a solved witness reaches
the requested target, pending futures are cancelled where possible. Processes
already executing may still finish before the pool exits.

Recommended run:

    mkdir -p python/Tromino/results/repair-depth/endpoint-d9-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 2000 \
      --steps 3000 \
      --warmup-flips 64 \
      --workers "$(nproc)" \
      --max-depth 10 \
      --target-depth 9 \
      --node-limit 1500000 \
      --base-seed 9000000 \
      --intermediate-policy endpoint \
      --search-objective resolved \
      --stop-on-target \
      --output python/Tromino/results/repair-depth/endpoint-d9-v24

After a target is found, replay the saved best resolved witness:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json \
      --min-depth 0 \
      --max-depth 11 \
      --node-limit 5000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/endpoint-d9-v24/replay-best-resolved.json

Freeze the next observation only after the replay verifies the depth frontier
and the geometry record is present.


## Seeded local W9 -> W10 campaign after OBS-006

OBS-006 established a replay-verified endpoint depth-nine witness at 24
vertices. Its critical repair footprint has graph radius two.

The next campaign stops restarting from fresh random planted maps. Instead each
job starts from the frozen W9 witness and explores legal preserving flips from
that known hard state.

The harness option is:

    --initial-witness PATH

When used, the output directory also receives `initial_witness.json`. Search
metadata record:

    initial_witness_seed
    initial_flip_history_length
    mutation_suffix_length

so a successful W10 witness can be compared directly with its W9 ancestor.

Recommended bounded first run:

    mkdir -p python/Tromino/results/repair-depth/seeded-w9-d10-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 64 \
      --steps 512 \
      --warmup-flips 0 \
      --workers "$(nproc)" \
      --max-depth 11 \
      --target-depth 10 \
      --node-limit 3000000 \
      --base-seed 10000000 \
      --intermediate-policy endpoint \
      --search-objective resolved \
      --stop-on-target \
      --initial-witness \
        python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json \
      --output python/Tromino/results/repair-depth/seeded-w9-d10-v24

This first run is intentionally much smaller than the fresh-random campaigns.
Every job begins already at a depth-nine hard state, so the goal is local wall
deepening rather than rediscovery of W9.

If target depth ten is found, replay:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/seeded-w9-d10-v24/best_resolved_witness.json \
      --min-depth 8 \
      --max-depth 11 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/seeded-w9-d10-v24/replay-best-resolved.json

Then compare the final witness flip history against
`initial_flip_history_length`. The suffix is the concrete mutation path from
the frozen W9 map toward its W10 descendant.

If the bounded 64 x 512 campaign does not find ten, preserve the result as a
local-search diagnostic and increase jobs/steps in a new output directory
rather than silently changing the existing experiment.


## Frontier-pressure W9 -> W10 campaign after OBS-007

The first seeded W9 campaign showed that `--search-objective resolved` is
misaligned once the required depth is already fixed at nine: it rewards more
repairs and more total repair moves, even when the critical depth-minus-one
frontier becomes easier.

The new mode is:

    --search-objective frontier

For a solved witness with required depth `d`, it ranks states by:

    1. required depth
    2. expanded states at ceiling d - 1
    3. fewer total repair moves as a final tie breaker

The depth-minus-one expansion is stored as `frontier_expanded`. The run also
writes:

    best_frontier_witness.json

Recommended bounded run:

    mkdir -p python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 32 \
      --steps 512 \
      --warmup-flips 0 \
      --workers "$(nproc)" \
      --max-depth 11 \
      --target-depth 10 \
      --node-limit 3000000 \
      --base-seed 11000000 \
      --intermediate-policy endpoint \
      --search-objective frontier \
      --stop-on-target \
      --initial-witness \
        python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json \
      --output python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24

The W9 baseline frontier is:

    required depth = 9
    depth-8 expanded = 202071

Even if W10 is not reached, an increase beyond `202071` is useful evidence
that the new objective is pushing in the intended direction.

If W10 is found, replay the frontier witness:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --min-depth 8 \
      --max-depth 11 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/replay-best-frontier.json

Promotion to the next observation requires either a replay-verified W10 witness
or a clearly larger W9 frontier that justifies a larger local-search budget.


## Second-generation frontier ascent after OBS-008

OBS-008 raised the verified W9 depth-minus-one frontier from `202071` to
`374152` using a descendant whose final graph differs from the original seed
by only two net diagonal flips.

The next campaign starts from that harder descendant rather than from the
original OBS-006 W9 map.

Recommended bounded run:

    mkdir -p python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24

    python3 python/Tromino/search/repair_depth_search.py search \
      --vertices 24 \
      --jobs 16 \
      --steps 384 \
      --warmup-flips 0 \
      --workers "$(nproc)" \
      --max-depth 11 \
      --target-depth 10 \
      --node-limit 3000000 \
      --base-seed 12000000 \
      --intermediate-policy endpoint \
      --search-objective frontier \
      --stop-on-target \
      --initial-witness \
        python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --output python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24

Baseline:

    required depth = 9
    frontier expanded = 374152

If the run reports a new frontier above `374152`, replay the best frontier
witness:

    python3 python/Tromino/search/repair_depth_search.py replay \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --min-depth 8 \
      --max-depth 11 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --trace \
      --stop-on-success \
      --output python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/replay-best-frontier.json

A W10 result is the primary target. A second frontier increase is also useful,
because it would show that local frontier amplification can be iterated rather
than occurring only once near the original W9 witness.


## Complete one-flip neighborhood census after OBS-009

OBS-009 found a W9 -> W10 transition produced by one preserving diagonal flip.
The next step is exhaustive over the immediate legal flip neighborhood rather
than stochastic.

The new command is:

    neighbors

It enumerates every move returned by `flippable_preserving()`, applies each
move once to the source witness, and evaluates the resulting graph in parallel.

For the OBS-008 source witness there are currently 17 legal preserving
one-flip neighbors, including the known depth-raising move
`[4,21,5,17]`.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-oneflip-neighborhood-v24

    python3 python/Tromino/search/repair_depth_search.py neighbors \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --max-depth 10 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --workers "$(nproc)" \
      --output python/Tromino/results/repair-depth/w9-oneflip-neighborhood-v24

Outputs:

    neighbors.jsonl
    summary.json
    best_depth_neighbor_witness.json
    best_frontier_neighbor_witness.json

The summary reports the complete depth histogram for resolved neighbors and
the classification counts for unresolved cases.

Primary checks:

    legal_preserving_neighbors = 17
    [4,21,5,17] occurs in neighbors.jsonl
    at least one neighbor has required_depth = 10

The main structural question is whether that depth-ten neighbor is unique. If
multiple one-flip moves reach ten, compare their affected quadrilaterals. If it
is unique, the flip `4-21 -> 5-17` becomes a sharper candidate for the local
wall-deepening gadget.

Any neighbor unresolved at ceiling ten should be replayed separately at a
higher ceiling before being interpreted as deeper than ten.
