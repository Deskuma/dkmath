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


## Repair-maze comparison after OBS-010

The one-flip census showed that the W9 source has exactly one ascending legal
neighbor and no level-nine neighbor. Every immediate neighbor still fails, at
its own depth-minus-one ceiling, at node 19 / restore step 16.

The next experiment compares the exchange-state maze on the two sides of the
unique depth-raising diagonal flip.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-w10-maze-compare-v24

    python3 python/Tromino/search/repair_depth_search.py maze-compare \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 10 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-w10-maze-compare-v24

Outputs:

    parent-profile.json
    child-profile.json
    comparison.json

The profile explores the exchange-state graph by BFS from the deterministic
colored state immediately before the blocker. Exit states are states in which
the current blocked vertex again has at least one safe color.

The main checks are:

    parent first exit depth = 9
    child first exit depth  = 10
    blocker = node 19 / step 16 on both sides

Then inspect the layer-by-layer differences. The target is to identify the
first layer at which the child loses parent exits or develops a different
Kempe-component branching structure.

This is the first direct attempt to turn the Collatz-like qualitative picture
into a concrete discrete dynamical-state comparison. It remains an algorithmic
experiment, not a claim of arithmetic equivalence with the Collatz map.


## Parent depth-nine exit replay after OBS-011

OBS-011 showed that the W9 parent has exactly two exits at depth nine while the
W10 child has none, despite the child having a smaller exchange-state maze.

The new command:

    exit-compare

extracts every parent exit at a selected depth and replays its exact Kempe
sequence against the child blocker state.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-w10-exit-compare-v24

    python3 python/Tromino/search/repair_depth_search.py exit-compare \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --exit-depth 9 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-w10-exit-compare-v24

Outputs:

    parent-exits.json
    child-exits.json
    comparison.json

Expected baseline:

    parent exit count = 2
    child exit count  = 0

For each parent exit, `comparison.json` records:

    complete parent Kempe path
    first unavailable exact move in the child
    same-color-pair child components at that point
    overlap with the parent component
    exact-prefix length before divergence

If both parent paths fail immediately for the same merged component, the current
wall-deepening mechanism becomes especially sharp:

    early preconditioning repair
    -> component merge
    -> both shallow exits deleted
    -> first exit moves from depth 9 to depth 10

If the two paths diverge for different reasons, keep the two obstructions
separate rather than forcing a single-gadget explanation.


## Topology/state intervention after OBS-012

OBS-012 showed that both parent depth-nine exits fail in the child because
their required (0,1) Kempe components are enlarged through vertices 4 and 17.

The next question is sufficiency: is the **child blocker colored state** enough
to force the deeper repair maze even if the graph topology is reverted to the
parent W9 graph?

The new command is:

    intervention-compare

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-w10-intervention-v24

    python3 python/Tromino/search/repair_depth_search.py intervention-compare \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 10 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-w10-intervention-v24

Outputs:

    Pgraph_Pstate.json
    Pgraph_Cstate.json
    Cgraph_Pstate.json
    Cgraph_Cstate.json
    comparison.json

Interpretation:

    Pgraph + Pstate = real W9 blocker state
    Cgraph + Cstate = real W10 blocker state
    Pgraph + Cstate = state-only intervention
    Cgraph + Pstate = topology-only intervention, only if proper/valid

The command checks each synthetic state before exploration. An improper crossed
coloring is reported as an invalid intervention rather than assigned a repair
depth.

The decisive field is:

    state_only_raises_parent_exit_depth

and, more strongly:

    state_only_matches_child_exit_depth

If both are true with first exit depth ten, then the preconditioned colored
state is sufficient to reproduce the depth jump on the parent topology.


## Partial blocker-state intervention after OBS-013

OBS-013 showed that the full child blocker state, transplanted onto the parent
graph, is already sufficient to move the first exit from depth nine to ten.

The remaining question is which part of that state change is necessary.

The new command:

    state-subsets

enumerates every subset of the parent-to-child blocker-state differences while
keeping the parent graph fixed.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-w10-state-subsets-v24

    python3 python/Tromino/search/repair_depth_search.py state-subsets \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 10 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-w10-state-subsets-v24

For the current pair the only differing blocker-state vertices are:

    vertex 4 : 1 -> 0
    vertex 17: 3 -> 1

so exactly four cases are evaluated:

    subset-none.json
    subset-4.json
    subset-17.json
    subset-4-17.json

The summary records validity, proper-coloring violations, first exit depth,
exit counts, maze size, and the minimal valid subsets that raise the baseline
exit depth.

A known static check is that changing only vertex 17 makes the parent coloring
improper on edge `4-17`; the command should therefore reject that cell rather
than assign it a repair depth.

The decisive unresolved case is `{4}`:

    if {4} alone raises 9 -> 10,
       vertex 4 recoloring is sufficient on the parent graph;

    if {4} remains at 9 but {4,17} reaches 10,
       the valid two-vertex state change is essential in this witness.


## Blocker-neighbor target-color scan after OBS-014

OBS-014 reduced the W9 -> W10 mechanism to a single valid recoloring on the
fixed parent graph:

    vertex 4 : 1 -> 0

The next question is whether vertex 4 is structurally unique.

The new command:

    target-pin-scan

reconstructs the blocker state, finds every unlocked colored neighbor of the
blocked vertex whose color differs from the requested target color, recolors
each candidate individually, validates the synthetic state, and explores its
repair maze.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-target0-pin-scan-v24

    python3 python/Tromino/search/repair_depth_search.py target-pin-scan \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --target-color 0 \
      --max-depth 10 \
      --node-limit 6000000 \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-target0-pin-scan-v24

For the current blocker node 19, the expected candidate vertices are:

    4, 5, 8, 9, 10, 13, 17, 18

The command also reconstructs the baseline shallow exit paths and records
whether each pinned vertex occurs in either parent depth-nine path.

Outputs:

    baseline.json
    baseline-exits.json
    pin-<vertex>-to-0.json
    summary.json

The decisive summary fields are:

    raising_vertices
    same_depth_vertices
    lowering_vertices
    invalid_vertices

If `raising_vertices == [4]`, the current one-point gadget is unusually
specific. If several neighbors raise depth, compare their relation to the two
baseline exit paths before promoting any structural rule.


## Full proper single-recolor scan after OBS-015

OBS-015 showed that vertex 4 is the only blocker neighbor that can be
individually recolored to target color 0 while preserving proper coloring.
That means the target-zero scan alone cannot tell whether vertex 4 is
dynamically special among multiple admissible pins.

The next command broadens the intervention space:

    single-recolor-scan

It enumerates every statically proper alternative color for every unlocked
colored blocker neighbor and evaluates each resulting blocker state.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-single-recolor-scan-v24

    python3 python/Tromino/search/repair_depth_search.py single-recolor-scan \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 10 \
      --node-limit 6000000 \
      --workers "$(nproc)" \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-single-recolor-scan-v24

The current W9 blocker has eleven statically proper one-point recolor candidates:

    4 : 1 -> 0
    4 : 1 -> 2
    5 : 3 -> 2
    9 : 1 -> 2
    10: 1 -> 2
    13: 3 -> 1
    13: 3 -> 2
    14: 0 -> 1
    14: 0 -> 2
    15: 0 -> 2
    17: 3 -> 2


Outputs include one profile per recoloring plus:

    baseline.json
    baseline-exits.json
    summary.json

The main classification fields are:

    raising_recolors
    same_depth_recolors
    lowering_recolors
    unresolved_recolors

This experiment tests whether the observed 9 -> 10 jump is specific to
recoloring vertex 4 into the shallow-exit target color, or is part of a broader
family of one-point blocker-state mutations.


## Full admissible blocker-state component after OBS-016

OBS-016 found a three-way valid one-step landscape around the W9 blocker:

    4 : 1 -> 0   depth 9 -> 10
    13: 3 -> 1   depth 9 -> 8
    14: 0 -> 1   depth 9 -> 8

Every statically proper recoloring to color 2 breaks the Missing-Color
invariant because all remaining vertices currently see palette `{0,1,3}`.

The next command explores the entire admissible connected component:

    state-component-scan

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-state-component-v24

    python3 python/Tromino/search/repair_depth_search.py state-component-scan \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 10 \
      --node-limit 6000000 \
      --state-limit 512 \
      --workers "$(nproc)" \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-state-component-v24

The command first enumerates every blocker-neighbor state reachable from the
baseline by one-vertex recolorings that preserve both:

    proper coloring
    Missing-Color invariant

Then it evaluates the repair maze at every state in parallel.

A static probe of the current witness found:

    admissible states = 32
    degree min        = 1
    degree max        = 5
    degree mean       = 3
    mutable color-2 states = 0

Outputs:

    state-000.json
    state-001.json
    ...
    summary.json

The summary includes the complete state graph, repair-depth distribution, edge
depth deltas, component degrees, and Hamming distance from the baseline state.

This is the first experiment that treats the blocker-state mechanism as an
actual finite dynamical landscape rather than isolated interventions.


## W10 admissible state component after OBS-017

OBS-017 completed the W9 blocker-state component and found a finite
unit-slope repair-depth landscape.

The same generic command can now be run on the actual W10 child witness.
Use a depth ceiling of 11 so a new depth-eleven state is not hidden.

Run:

    mkdir -p python/Tromino/results/repair-depth/w10-state-component-v24

    python3 python/Tromino/search/repair_depth_search.py state-component-scan \
      python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
      --step 16 \
      --prefix-depth 10 \
      --max-depth 11 \
      --node-limit 6000000 \
      --state-limit 512 \
      --workers "$(nproc)" \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w10-state-component-v24

A static proper + Missing-invariant enumeration of the W10 blocker state gives:

    admissible states = 4
    edges             = 3
    degree range      = 1..2

The component is a four-state path. The actual repair-depth evaluation is still
required.

Compare its `summary.json` against:

    python/Tromino/results/repair-depth/w9-state-component-v24/summary.json

especially:

    depth_counts
    min_first_exit_depth
    max_first_exit_depth
    edge_depth_deltas

If a depth-eleven state appears, the state-space mechanism itself has extended
the earlier 9 -> 10 jump. If not, the result still provides an independent
test of the observed unit-slope law.


## Preserving-flip chamber census after OBS-018

OBS-018 showed that the actual W10 blocker-state component is exactly a
four-state induced sector of the complete W9 component.

The new command:

    flip-chamber-census

tests whether this kind of chamber sectorization is common across all legal
preserving one-flip neighbors of W9.

Run:

    mkdir -p python/Tromino/results/repair-depth/w9-flip-chamber-census-v24

    python3 python/Tromino/search/repair_depth_search.py flip-chamber-census \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --source-component-summary python/Tromino/results/repair-depth/w9-state-component-v24/summary.json \
      --step 16 \
      --prefix-depth 10 \
      --node-limit 6000000 \
      --state-limit 512 \
      --workers "$(nproc)" \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-flip-chamber-census-v24

For each preserving flip the command restores the blocker prefix and performs
only the cheap static admissible-state enumeration. It does not evaluate the
full repair maze at every child state.

Outputs:

    neighbor-00.json
    neighbor-01.json
    ...
    summary.json

The key aggregate fields are:

    child_projection_subset_count
    induced_subgraph_match_count
    predicted_sector_match_count
    blocker_adjacency_changed_count

Each neighbor record also contains the removed and added edges, blocker-state
changes, overlap with the 32 W9 states, and the connected sectors obtained by
filtering the W9 chamber through the new-edge properness constraint.

The W10 move `[4,21,5,17]` should act as the calibration case: its child
component should match the predicted W9 sector `{8,10,12,14}`.


## Correction: rerun the preserving-flip chamber census

The first census run revealed a bug only in the parent-sector predictor:
the connected-component queue used a fixed-length loop. Child chamber
enumeration itself was unaffected.

The corrected implementation:

- traverses filtered parent components completely;
- validates every W9 projection directly in the **full child context**;
- records `child_admissible_parent_components`;
- records the sector containing the child baseline;
- reports `child_matches_child_admissible_sector`;
- aggregates `child_admissible_sector_match_count`.

Rerun the same command and overwrite:

    python3 python/Tromino/search/repair_depth_search.py flip-chamber-census \
      python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
      --source-component-summary python/Tromino/results/repair-depth/w9-state-component-v24/summary.json \
      --step 16 \
      --prefix-depth 10 \
      --node-limit 6000000 \
      --state-limit 512 \
      --workers "$(nproc)" \
      --intermediate-policy endpoint \
      --output python/Tromino/results/repair-depth/w9-flip-chamber-census-v24

A recomputation from the already pushed component files gives six exact
child-admissible sector matches (neighbor indices 1, 3, 11, 13, 14, 16), so
the corrected rerun should reproduce that calibration.
