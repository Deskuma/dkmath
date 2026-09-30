# Tromino Eisenstein Texture Simulation Roadmap

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

Base:

```text
develop
```

## Scope

This branch starts the Python simulation track for the Tromino exchange /
Eisenstein-texture approach.

The work is deliberately staged so that geometric realization, texture
alignment, and coloring search are not mixed before their individual failure
modes are understood.

The central experimental question is:

> Given a finite planar embedded adjacency structure, can a four-state coloring
> be reached and maintained by a controlled family of local exchange moves, and
> what structural invariant distinguishes successful from stalled instances?

The branch does not claim a Four Color Theorem proof.

## EXP-000 — scaffold and exact baseline

Status: planned.

Implement the minimal data model for a planar embedded region graph:

- node identifiers,
- undirected adjacency,
- cyclic neighbor order,
- optional outer-boundary marker,
- four-state color index `{0, A, B, C}`.

Implement validation for:

- symmetry of adjacency,
- no accidental self-adjacency unless explicitly allowed by a test,
- cyclic-order consistency,
- proper-coloring predicate.

Implement a small exact four-color backtracking solver.

Purpose:

- provide an oracle for later heuristic experiments,
- save exact witnesses for small instances,
- distinguish solver failure from instance/model failure.

## EXP-001 — random planar / triangulated instances

Status: planned.

Generate reproducible planar embedded inputs from a construction that preserves
planarity by design.

Preferred first generator:

1. begin from a triangle,
2. select a triangular face,
3. insert a new node in that face,
4. connect it to the three face vertices,
5. update the rotation / cyclic-order data,
6. repeat from a fixed random seed.

Optional later variation:

- legal edge flips,
- controlled deletion / contraction experiments,
- explicit outer-boundary generation.

Record:

- seed,
- `|V|`,
- `|E|`,
- degree distribution,
- maximum degree,
- boundary size when present.

Do not use unrestricted random graphs as the primary generator.

## EXP-002 — GapSwap move laboratory

Status: planned after EXP-000/001.

Start from deliberately conflicted four-state assignments.

Define a small explicit move family before introducing complicated heuristics.
Candidate moves include:

- single-node recolor when a free color exists,
- two-state exchange on a connected component,
- local V4 delta shift on a connected patch,
- small cycle / face correction.

For each move, record:

- changed node set,
- conflicts removed,
- conflicts introduced,
- boundary-condition effect,
- reversibility,
- whether the move can be represented as the current Tromino exchange law.

Primary objective:

```text
reach conflict_count = 0
```

Secondary objectives such as minimum swap count are deferred.

Always compare with the exact oracle for small instances.

## EXP-003 — outer-sea / three-color boundary constraint

Status: planned.

Fix the outer sea to state `0`.

Require every region adjacent to the outer sea to use only

```text
{A, B, C}
```

Investigate the working heuristic:

- use `A/B` alternation where possible,
- introduce `C` as a repair state,
- preserve one free state as an interior Gap when possible.

Questions to measure:

- when does a raw assignment expose all four states on an interface?
- can local exchange reduce the boundary palette to at most three states?
- what is the smallest exact-oracle-solvable instance where the chosen
  GapSwap strategy stalls?
- are stalled cases characterized by parity, degree, cyclic order, or a
  specific separator structure?

This experiment is the first direct test of the proposed
"boundary palette compression" interpretation of GapSwap.

## EXP-004 — tree / cotree search strategy

Status: planned.

Treat a spanning tree as the propagation backbone and non-tree edges as
consistency constraints.

Compare at least:

- BFS / radial tree,
- DFS tree,
- low-stretch-oriented tree heuristics.

For every non-tree edge `u-v`, measure the tree distance

```text
d_T(u, v)
```

and the resulting fundamental-cycle size.

Candidate tree cost:

```text
sum_{e notin T} d_T(e)
```

and separately the maximum fundamental-cycle stretch.

Measure whether shorter fundamental cycles reduce GapSwap repair cost or
failure rate.

A tree is an algorithmic scaffold only; the original non-tree edges and cyclic
order must remain present.

## EXP-005 — high-degree "breathing point" normalization

Status: planned.

Test the proposed rule for regions whose local contact count exceeds the simple
Eisenstein neighborhood capacity.

Represent one original region by one macro identity but allow a connected
triangular support patch with multiple boundary ports.

First self-similar candidate:

```text
capacity(k) = 3 * 2^k
```

Choose the least `k` with

```text
degree(v) <= capacity(k)
```

and preserve the original cyclic order of neighbor ports.

Questions:

- is port capacity alone sufficient for local realization?
- what extra constraints are needed for neighboring macro patches to connect
  without crossing?
- which failures come from degree and which come from rotation-system data?
- does a different growth law produce smaller or more stable realizations?

This stage should explicitly separate:

- graph-coloring success,
- combinatorial port realization,
- flat geometric realization.

## EXP-006 — Trigon macro-map realization

Status: planned after the abstract solver is stable.

Convert an embedded abstract instance into a triangular macro map.

Each original region keeps:

- one macro identity,
- one representative point / centroid,
- one macro color,
- ordered boundary ports.

The micro-triangle patch is support geometry only.

Test separately:

1. arbitrary triangular support,
2. equal-area macro normalization,
3. regular / Eisenstein-compatible realization.

Do not assume these three realization levels are equivalent.

Save counterexamples separately for:

- adjacency loss,
- cyclic-order loss,
- crossing,
- flat-lattice obstruction.

## EXP-007 — Eisenstein texture baseline

Status: planned.

Introduce a periodic Eisenstein / triangular-lattice four-state texture.

For each macro region representative point `b(v)`, read an initial state

```text
t(v) = Texture(b(v))
```

and compare it with:

- random initial coloring,
- greedy initial coloring,
- boundary-conditioned initial coloring.

Measure:

- initial conflict count,
- number of corrections,
- correction component size,
- failure rate,
- sensitivity to texture translation,
- sensitivity to rotation / reflection,
- global V4 phase shift.

The texture is an initial condition / baseline field.  A successful experiment
must still verify proper coloring on the original adjacency structure.

## EXP-008 — phase correction and path reconstruction

Status: later research.

Represent the corrected macro state as

```text
color(v) = texture(v) + phi(v)
```

and analyze the correction field `phi`.

Questions:

- does a successful correction admit a compact decomposition into GapSwap
  moves?
- can the move sequence be reconstructed as a tetrahedral rolling history?
- are multiple histories equivalent under cancellation / backtracking?
- which part of the history is invariant and which is gauge?

Path reconstruction is explanatory.  It is not a prerequisite for the coloring
solver.

## Experiment record policy

Every committed experiment must be reproducible.

Use a layout such as

```text
experiments/exp-XXX/
  README.md
  config.json
  summary.json
  failures.jsonl
  figures/
```

The report should distinguish:

- observation,
- heuristic interpretation,
- conjectured invariant,
- exact-oracle fact,
- Lean-formalized fact.

Do not promote a numerical observation directly to a theorem statement.

## Promotion to Lean

A Python result becomes a Lean candidate only after:

1. the invariant can be stated without reference to random seeds or numerical
   optimization,
2. the statement is stable across independent generated instances,
3. boundary assumptions and embedding assumptions are explicit,
4. the result is not merely a property of the chosen heuristic.

The intended endpoint is to feed structurally justified lemmas back into
`DkMath.Tromino`, especially toward the remaining universal
all-triangular genus-zero tetrahedral assignment target.

## Codex instruction

Not fixed yet.

The implementation instruction will be written after the first interactive
scratch experiments determine:

- the initial move family,
- the exact data-model fields,
- the first measurable failure question,
- the result-file format that is worth preserving.

This avoids freezing an implementation strategy before the puzzle mechanics are
understood.


## Recorded scratch observation

### OBS-001 — Missing-Color Lift

Status: recorded on 2026-09-28.

Files:

```text
python/Tromino/experiments/OBS-001-MissingColorLift/
  README.md
  summary.json
  scratch_obs001.py
```

The first frozen observation separates three facts:

- a degree-3 restore step automatically leaves at least one of four colors
  missing, but 3-peeling barely simplifies the tested Delaunay instances;
- degree 4 is the first local restore threshold where the already-colored
  boundary can contain all four colors;
- a heuristic that explicitly protects future missing colors avoids some dead
  branches that plain greedy enters, but it is not sufficient by itself.

The explicit seed `120001` records a branch where plain greedy chooses one of
two legal colors and later reaches a node with boundary palette
`{0,1,2,3}`, while the missing-color-aware branch completes.

This motivates the next experimental invariant:

```text
for every not-yet-restored node v:
    |P(v)| <= 3
```

where `P(v)` is the set of colors already visible on the restored boundary of
`v`.

The next solver experiment should preserve this invariant whenever a direct
choice exists and invoke a genuine GapSwap repair only when every direct choice
would violate it.

OBS-001 is a scratch observation, not a theorem and not yet a claim about
quantum advantage.


### OBS-002 — Missing-Color Invariant with Forced Local Exchange

Status: recorded on 2026-09-28.

Files:

~~~
python/Tromino/experiments/OBS-002-MissingColorForcedExchange/
  README.md
  summary.json
  scratch_obs002.py
~~~

OBS-002 modifies the lift rule so that a direct color is accepted only when it
preserves the Missing-Color Invariant for all not-yet-restored nodes. A
two-color Kempe-component exchange is used only when no direct safe color
exists. The exchange is a diagnostic proxy for a future DkMath GapSwap, not an
identification with the formal exchange law.

Frozen observations:

- direct invariant-preserving lift still stalls as size grows;
- one exchange layer removes most stalls;
- depth two solved every recorded instance up through the 200-node batches;
- in a dedicated 500-node batch, depth two solved 49/50 instances;
- seed 5200005 is an explicit depth-three witness;
- depth three solved all 50 instances in that 500-node batch.

The current quantity of interest is therefore not total coloring search-space
size alone, but the local repair-depth function

~~~
D(n) = maximum repair depth observed at size n.
~~~

This weakens the naive quantum-search motivation: a useful structural invariant
can collapse a large global search into shallow local repair. The next experiment
should use adversarial / planted tetrahedral refinements and actively search for
the smallest depth-four witness rather than merely increasing random instance
size.

No universal repair-depth bound and no quantum advantage are claimed.


### Long-run adversarial repair-depth search

Status: harness prepared on 2026-09-28.

Files:

    python/Tromino/search/README.md
    python/Tromino/search/repair_depth_search.py

The long-run harness starts from a planted tetrahedral / four-state solution,
adds resolution by triangular face subdivision, and adds maze-like
combinatorial walls by solution-preserving diagonal edge flips.

The solver is not given the planted coloring. It restores vertices in birth
order, attempts to preserve the Missing-Color Invariant, and uses two-color
Kempe-component exchange as the current GapSwap proxy only when direct lifting
stalls.

The primary search target is now a verified repair depth 5 witness. Unresolved
cases are classified separately as depth-limited, node-limited, or exhausted
under the current strict invariant and proxy move set. An unresolved case is not
silently promoted to a deeper witness.

The script is designed for development-PC runs with multiprocessing,
crash-safe JSONL checkpoints, resumable deterministic seeds, best-witness
serialization, and witness replay at larger depth ceilings. Raw runs.jsonl is
ignored by default; compact summary and witness files can be committed or
returned through chat.

A second endpoint repair policy is included specifically to test whether a hard
case represents a deeper local maze or instead shows that strict intermediate
Missing-Color preservation is too restrictive.


### OBS-003 — Endpoint Gap Restoration

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-003-EndpointGapRestoration/
  README.md
  summary.json
```

OBS-003 records two complementary witnesses from the long-run planted
adversarial search.

First, seed `6000915` is a replay-verified strict repair-depth six witness:
depth ceilings 0 through 5 fail and depth 6 succeeds. Under the present
generator, restore order, locked frame, and Kempe-component exchange proxy, this
gives the observation `D_strict(24) >= 6`.

Second, seed `6000596` is `state_space_exhausted` under the strict
intermediate Missing-Color policy, with `hit_depth_limit = false`, but the
same saved witness is solved by the endpoint policy at repair depth 3.

This separates two notions:

```text
strict repair:
    every primitive exchange state must satisfy Missing-Color safety

endpoint repair:
    only the composite repair start/end states must satisfy it
```

The current interpretation is that Missing Color may be a boundary condition of
a composite Gap repair rather than a state invariant required after every
primitive exchange. This is an experimental interpretation, not yet a theorem
or the final DkMath GapSwap definition.

The next long-run campaign should therefore optimize directly for
`D_endpoint(G)` and search for a verified endpoint-depth hierarchy.


### Next campaign — endpoint repair-depth hierarchy

Status: ready to run after OBS-003.

The search harness now supports `--search-objective resolved` and writes
separate best-resolved and best-unresolved witnesses. This avoids the OBS-003
long-run issue where an unresolved strict witness could replace the deepest
verified solved witness in `best_witness.json`.

The first endpoint-primary campaign is:

```text
vertices            = 24
jobs                = 2000
steps               = 2000
warmup_flips        = 48
max_depth           = 8
target_depth        = 6
node_limit          = 750000
base_seed           = 7000000
intermediate_policy = endpoint
search_objective    = resolved
```

Primary question:

```text
How large can verified D_endpoint(G) become while the planted solution
lineage remains intact?
```

The campaign should be promoted to the next OBS record only after replay of the
best resolved witness confirms failure at depth `d-1` and success at depth
`d`.


### OBS-004 — Endpoint Repair Depth Seven

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-004-EndpointRepairDepthSeven/
  README.md
  summary.json
```

The first endpoint-primary resolved-depth campaign completed 2000/2000 jobs as
solved and produced a replay-verified depth-seven witness at 24 vertices.

Seed `7001217` fails under endpoint repair ceilings 0 through 6 and succeeds
at depth 7. The critical repair is at restore step 18, node 21.

Thus the current experimental frontier is:

```text
D_endpoint(24) >= 7
```

for the present planted generator, deterministic restore order, locked frame,
direct-choice rule, and Kempe-component exchange proxy.

This shows that the deep-repair phenomenon does not disappear when
Missing-Color safety is relaxed from a per-primitive state invariant to a
composite-repair endpoint condition.

### Next campaign — fixed-size endpoint depth 8

Before increasing graph size, keep `n = 24` and ask whether wall arrangement
alone can raise the verified endpoint repair depth.

Planned campaign:

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

If a depth-eight witness is replay-verified, continue at fixed size before
moving to larger maps. If the frontier remains at seven after this larger
search, compare 28- and 32-vertex campaigns to test size dependence.


### OBS-005 — Pure Endpoint Repair Depth Eight

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-005-PureEndpointRepairDepthEight/
  README.md
  summary.json
```

Seed `8000005` gives a particularly clean fixed-size witness:

```text
vertices           = 24
repair events      = 1
required depth     = 8
repair moves total = 8
depth 7            = depth_limited
depth 8            = solved
```

The depth-eight repair uses component sizes:

```text
2, 1, 1, 2, 2, 1, 4, 4
```

so the current deepest witness is produced by a composition of several small
component exchanges rather than one large Kempe component.

The replay-verified frontier is now:

```text
D_endpoint(24) >= 8
```

for the current planted generator, deterministic restore order, locked frame,
direct-choice rule, and Kempe-component proxy.

This motivates separating repair depth from geometric locality.

### Next campaign — endpoint depth nine with repair geometry

The search harness now records geometry for every traced successful repair:

```text
component_sizes
max_component_size
footprint_vertices
footprint_size
min_distance_from_current
max_distance_from_current
```

It also supports:

```text
--stop-on-target
```

which cancels pending jobs where possible once a solved witness reaches the
requested target depth.

The next fixed-size campaign keeps `n = 24`:

```text
vertices            = 24
jobs                = 2000
steps               = 3000
warmup_flips        = 64
max_depth           = 10
target_depth        = 9
node_limit          = 1500000
base_seed           = 9000000
intermediate_policy = endpoint
search_objective    = resolved
stop_on_target      = true
```

Primary questions:

```text
1. Can D_endpoint(24) reach 9?
2. Does deeper repair require larger components?
3. Does the union footprint grow with depth?
4. Does the graph radius from the blocked node grow with depth?
```

The next OBS record should be frozen only after replay confirms failure at
depth `d-1`, success at depth `d`, and records the repair-geometry metrics.


### OBS-006 — Radius-Two Endpoint Repair Depth Nine

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-006-RadiusTwoEndpointRepairDepthNine/
  README.md
  summary.json
```

Seed `9000035` is replay-verified:

```text
depth 8 = depth_limited, expanded 202071
depth 9 = solved,        expanded 202085
```

The critical depth-nine repair occurs at node `19`, restore step `16`.
Its geometry is:

```text
component sizes          = 9,1,2,1,1,1,3,2,2
max component size       = 9
footprint size           = 15
distance from blocker    = 1..2
```

Thus the current experimental frontier is:

```text
D_endpoint(24) >= 9
```

while the entire critical repair footprint still lies within graph radius two
of the blocked node.

This is evidence for a deep local exchange maze in the present solver model,
not a universal radius-two theorem.

### Next campaign — seeded W9 -> W10 local deepening

The search harness now accepts:

```text
--initial-witness PATH
```

Every job may therefore start from the same verified hard witness instead of a
fresh planted triangulation. The initial witness is copied into the output
directory, and the result metadata records the original flip-history length and
the mutation-suffix length.

The next question is:

```text
Can local solution-preserving flips deepen the known W9 wall into W10?
```

Start from:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json
```

and keep `warmup_flips = 0` so the recorded mutation suffix is directly
interpretable as a path away from W9.

Initial campaign:

```text
vertices            = 24
jobs                = 64
steps               = 512
warmup_flips        = 0
max_depth           = 11
target_depth        = 10
node_limit          = 3000000
base_seed           = 10000000
intermediate_policy = endpoint
search_objective    = resolved
stop_on_target      = true
initial_witness     = W9 / seed 9000035
```

If a W10 descendant is found, replay it and inspect the mutation suffix between
the frozen W9 seed and the first W10 witness. That suffix becomes candidate data
for a recursive wall-deepening gadget.

If this bounded local campaign does not reach ten, enlarge the local search
budget before returning to fresh random planted starts.


### OBS-007 — Stable Depth-Nine Basin under Naive Seeded Objective

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-007-StableDepthNineBasin/
  README.md
  summary.json
```

The first W9-seeded local campaign completed 64/64 jobs with:

```text
mean resolved depth = 9
max resolved depth  = 9
target depth 10     = not found
```

The old resolved objective selected seed `10000057` because it increased
repair count and total repair moves, but its critical depth-eight frontier
expanded only `194765` states, versus `202071` for the original OBS-006 W9
seed.

Thus the selected descendant was globally busier but not harder at the
critical wall.

The next search objective is therefore the **frontier objective**:

```text
(required depth, depth-minus-one frontier expansion)
```

with witness cleanliness only as a final tie breaker.

### Next campaign — W9 frontier pressure toward W10

The harness now accepts:

```text
--search-objective frontier
```

For a solved witness of required depth `d`, the primary secondary score is the
number of states expanded when the same map is tested at ceiling `d - 1`.

The search writes:

```text
best_frontier_witness.json
```

and records `best_frontier_seed`, `best_frontier_depth`, and
`best_frontier_expanded` in the summary.

Use the original OBS-006 W9 witness again:

```text
python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json
```

Bounded first campaign:

```text
vertices            = 24
jobs                = 32
steps               = 512
warmup_flips        = 0
max_depth           = 11
target_depth        = 10
node_limit          = 3000000
base_seed           = 11000000
intermediate_policy = endpoint
search_objective    = frontier
stop_on_target      = true
initial_witness     = OBS-006 W9 / seed 9000035
```

Success criterion remains replay-verified depth ten. If no W10 descendant is
found, compare the best frontier expansion against the W9 baseline `202071`
before deciding whether to enlarge the local budget.


### OBS-008 — Two-Flip Frontier Amplification

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-008-TwoFlipFrontierAmplification/
  README.md
  summary.json
```

Starting from the OBS-006 W9 witness, frontier search found seed `11000009`:

```text
required depth      = 9
depth-8 expanded    = 374152
critical footprint  = 13
max component size  = 6
critical radius     = 2
```

The previous W9 baseline was `202071`, so the critical depth-eight frontier
increased by `172081`.

The final hard descendant differs from the seed by two net diagonal flips. The
recorded four-flip suffix contains one immediate inverse pair.

This is the first direct evidence that a very small local map mutation can
strongly amplify frontier hardness while leaving required depth and graph
radius unchanged.

### Next campaign — second-generation frontier ascent

Use the OBS-008 best frontier witness as the next initial state:

```text
python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json
```

The new baseline is:

```text
required depth = 9
frontier       = 374152
```

Run a smaller second-generation campaign before increasing the budget:

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
initial_witness     = OBS-008 best frontier / seed 11000009
```

Promote the result if either:

```text
1. a replay-verified W10 descendant is found, or
2. the verified W9 frontier exceeds 374152.
```

The search summary now also records the best frontier seed/depth/expanded fields
for both periodic and final summaries.


### OBS-009 — Single-Flip Depth Jump Nine to Ten

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-009-SingleFlipDepthJumpNineToTen/
  README.md
  summary.json
```

Starting from the OBS-008 frontier-amplified W9 witness, seed `12000006`
reaches replay-verified depth ten after one accepted preserving diagonal flip:

```text
[4,21,5,17]
```

which replaces diagonal `4-21` by `5-17`.

Replay:

```text
depth 8  = depth_limited, expanded 264302
depth 9  = depth_limited, expanded 279278
depth 10 = solved
```

The critical depth-ten repair still has graph radius two.

Harness-relative statement:

```text
D_endpoint^H(G_12000006) = 10
```

### Next experiment — complete one-flip neighborhood of W9

A new `neighbors` subcommand enumerates every legal
planted-color-preserving one-flip neighbor of a saved witness and evaluates
each under the repair harness.

For the OBS-008 W9 frontier witness, the current graph has exactly 17 legal
preserving one-flip neighbors. The known depth-raising move
`[4,21,5,17]` is among them.

The experiment should classify the complete local neighborhood:

```text
depth < 9
depth = 9
depth = 10
unresolved at ceiling 10
```

and determine whether the known W9 -> W10 flip is unique among all legal
one-flip moves.


### OBS-010 — Unique Ascending Edge in the W9 One-Flip Neighborhood

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-010-UniqueAscendingEdge/
  README.md
  summary.json
```

The complete legal preserving one-flip neighborhood of the OBS-008 W9 witness
contains 17 graphs with depth histogram:

```text
10: 1
 9: 0
 8: 3
 7: 3
 6: 6
 5: 2
 4: 2
```

The unique ascending edge is:

```text
[4,21,5,17]
4-21 -> 5-17
```

All 17 neighbors retain the same critical restore location:

```text
node 19 / step 16
```

so the local flips alter the exchange-state maze depth rather than moving the
blocker.

The Collatz resemblance is recorded only as a qualitative dynamical analogy:
local transitions can sharply raise or lower a scalar complexity. No arithmetic
equivalence is asserted.

### Next experiment — repair-maze parent/child comparison

The harness now provides:

```text
maze-compare PARENT CHILD
```

It reconstructs the deterministic restore state immediately before a selected
step, then explores the Kempe-exchange state graph layer by layer.

Recorded data include:

```text
generated states per depth
processed states per depth
invariant-valid states per depth
exit states per depth
duplicate transitions per depth
Kempe moves examined per depth
first successful exit depth and path
prefix repair history
colored-state difference
graph edge difference
blocker-neighbor difference
```

The next comparison is the unique W9 -> W10 transition at node 19 / step 16.


### OBS-011 — Preconditioning Repair Deletes the Depth-Nine Exits

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-011-PreconditioningRepairDeletesDepthNineExits/
  README.md
  summary.json
```

Direct repair-maze comparison across the unique W9 -> W10 flip shows:

```text
parent first exit depth = 9
child first exit depth  = 10

depth 9 exits:
  parent = 2
  child  = 0
```

The child exchange-state maze is smaller overall, so the depth increase is
best described as shallow-exit annihilation rather than maze growth.

The diagonal flip does not change blocker node 19 adjacency. Instead it induces
an earlier repair at step 14 / node 17, changing colors at vertices 4 and 17
before the solver reaches node 19. This reconnects several Kempe components,
including the parent (0,1) components `{4}` and
`{8,9,10,11,12,15}`.

### Next experiment — replay both parent depth-nine exits on the child

The harness now provides:

```text
exit-compare PARENT CHILD
```

It exhaustively extracts all parent exits at a chosen repair depth, reconstructs
their exact Kempe paths, and attempts to replay those paths against the child
blocker state.

For each parent path it records the first exact move that is no longer
available in the child, together with overlapping child components of the same
color pair.

Primary question:

```text
Do both parent depth-nine exits die at the same early component
reconnection, or at distinct obstructions?
```


### OBS-012 — Common (0,1) Component Fusion Kills Both Depth-Nine Exits

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-012-Common01ComponentFusion/
  README.md
  summary.json
```

Both parent depth-nine exits are destroyed in the W10 child by enlargement of
a parent (0,1) Kempe component through vertices 4 and 17.

The two exits diverge at different positions:

```text
exit 0: divergence at move 0
exit 1: divergence at move 2
```

but the common obstruction is the same kind of (0,1) component fusion.

### Next experiment — topology/state intervention

The harness now provides:

```text
intervention-compare PARENT CHILD
```

At the blocker it crosses parent/child graph topology with parent/child colored
state:

```text
Pgraph + Pstate
Pgraph + Cstate
Cgraph + Pstate
Cgraph + Cstate
```

Each crossed state is checked for properness and the Missing-Color invariant
before the repair maze is explored.

The key test is whether `Pgraph + Cstate` already has first exit depth ten.
That would show that the preconditioned blocker state is sufficient, within the
fixed parent topology, to reproduce the depth jump.

The converse crossed cell `Cgraph + Pstate` is expected to be invalid if the
added edge `5-17` joins two equally colored parent-state vertices; the command
records such invalidity rather than interpreting it as a repair-depth result.


### OBS-013 — Blocker State Alone Reproduces the Depth Jump

Status: recorded on 2026-09-29.

Files:

```text
python/Tromino/experiments/OBS-013-BlockerStateSufficiency/
  README.md
  summary.json
```

The topology/state intervention gives:

```text
Pgraph + Pstate -> first exit depth 9
Pgraph + Cstate -> first exit depth 10
Cgraph + Cstate -> first exit depth 10
```

while `Cgraph + Pstate` is invalid because edge `5-17` joins two
parent-state color-3 vertices.

Thus the child blocker colored state is sufficient, on the fixed parent graph,
to delete both depth-nine exits and reproduce the depth-ten first exit.

### Next experiment — partial blocker-state subsets

The harness now provides:

```text
state-subsets PARENT CHILD
```

It finds every blocker-state vertex whose color differs between parent and
child, then enumerates every subset of those parent-to-child recolorings on the
fixed parent graph.

For the current witness pair the differing vertices are exactly:

```text
4  : 1 -> 0
17 : 3 -> 1
```

so the experiment evaluates:

```text
{}
{4}
{17}
{4,17}
```

Every synthetic state is checked for properness and the Missing-Color invariant
before repair depth is interpreted.

The main target is the set of minimal valid recoloring subsets that raise the
first exit depth above nine.


### OBS-014 — Single Vertex Recoloring Is Sufficient

Status: recorded on 2026-09-30.

Files:

```text
python/Tromino/experiments/OBS-014-SingleVertexRecoloringSufficient/
  README.md
  summary.json
```

On the fixed parent W9 graph, the unique minimal valid subset of the blocker
state differences that raises the first exit depth is:

```text
{4}
```

with the single recoloring:

```text
vertex 4 : 1 -> 0
```

This alone changes:

```text
first exit depth: 9 -> 10
depth-9 exits:     2 -> 0
depth-10 exits:    4 -> 4
```

The full-child (0,1) component fusion observed earlier is therefore not
necessary for the depth jump.

The two parent depth-nine exits are killed differently by the same one-vertex
change: one path remains executable but fails to open candidate color 0 because
vertex 4 remains a color-zero blocker neighbor; the other loses a later Kempe
component after vertex 4 leaves the relevant color pair.

### Next experiment — target-color pin scan

The harness now provides:

```text
target-pin-scan WITNESS
```

It keeps the witness graph and blocker state fixed, then recolors each unlocked
colored blocker neighbor individually to a selected target exit color.

For the current W9 blocker and target color 0, the candidates are the eight
nonzero unlocked colored neighbors:

```text
4, 5, 8, 9, 10, 13, 17, 18
```

Each synthetic state is checked for properness and the Missing-Color invariant.

The experiment asks whether vertex 4 is unique among one-point target-color
pins, or belongs to a larger family of blocker-neighbor pins that raise the
first exit depth.


### OBS-015 — Unique Proper Target-Color Pin Site

Status: recorded on 2026-09-30.

Files:

```text
python/Tromino/experiments/OBS-015-UniqueProperTargetPin/
  README.md
  summary.json
```

For target color 0 at blocker node 19, the tested nonzero unlocked neighbors
were:

```text
4, 5, 8, 9, 10, 13, 17, 18
```

Only vertex 4 can be recolored to 0 while preserving proper coloring.
That unique valid target-zero pin raises the first exit depth from 9 to 10.

The other seven candidates are rejected before maze dynamics because they are
adjacent to already-colored zero vertices.

Therefore the current uniqueness is a feasibility uniqueness, not yet a
dynamical comparison among several valid target-color pins.

### Next experiment — all proper one-point recolorings

The harness now provides:

```text
single-recolor-scan WITNESS
```

It enumerates every statically proper alternative color for every unlocked
colored blocker neighbor, then evaluates each synthetic state.

This broadens the question from:

```text
which neighbor can be pinned to exit color 0?
```

to:

```text
which proper one-point recolorings raise, preserve, or lower repair depth?
```

For the current W9 blocker the statically proper alternatives include:

```text
4  : 1 -> 0,2
5  : 3 -> 2
9  : 1 -> 2
10 : 1 -> 2
13 : 3 -> 1,2
14 : 0 -> 1,2
15 : 0 -> 2
17 : 3 -> 2
```

Vertices 8, 12, and 18 have no proper alternative color.


### OBS-016 — Admissible One-Point State Landscape

Status: recorded on 2026-09-30.

Files:

```text
python/Tromino/experiments/OBS-016-AdmissibleOnePointStateLandscape/
  README.md
  summary.json
```

The complete statically proper one-point recolor scan around the W9 blocker
finds only three Missing-Color-valid moves:

```text
4  : 1 -> 0   depth 9 -> 10
13 : 3 -> 1   depth 9 -> 8
14 : 0 -> 1   depth 9 -> 8
```

All eight other statically proper alternatives are recolorings to color 2 and
break the Missing-Color invariant.

At the baseline state, every remaining vertex 19..23 has palette `{0,1,3}`.
Color 2 is therefore the common missing future color.

A static connected-component enumeration under proper + Missing-valid
one-point recolorings gives exactly 32 states, degree range 1..5, mean degree
3, and no reachable mutable-neighbor state using color 2.

### Next experiment — full admissible blocker-state component

The harness now provides:

```text
state-component-scan WITNESS
```

It enumerates the complete connected component of admissible blocker-neighbor
colored states reachable by one-point recolorings, then evaluates repair depth
at every state.

The current W9 component is expected to contain 32 states.

The resulting graph will allow direct inspection of:

```text
repair-depth distribution
local minima / maxima
edge depth changes
cycles
distance from the W9 baseline
whether the observed +/-1 local motion persists globally
```


### OBS-017 — Finite Unit-Slope Repair Landscape

Status: recorded on 2026-09-30.

Files:

```text
python/Tromino/experiments/OBS-017-FiniteUnitSlopeRepairLandscape/
  README.md
  summary.json
```

The complete W9 admissible blocker-state component contains 32 states and 48
one-point recoloring edges. Repair first-exit depth takes only the values
8, 9, and 10 with distribution:

```text
8 : 9 states
9 : 19 states
10: 4 states
```

Every admissible state edge satisfies:

```text
|delta first-exit-depth| <= 1
```

with 19 flat edges and 29 unit-slope edges.

This is a complete finite observation for the witness, not yet a general
theorem.

### Next experiment — W10 complete state component

Repeat `state-component-scan` on the actual W10 child witness with
`--max-depth 11`.

A static admissibility probe gives only four states and three edges, forming a
simple path. This sharply contrasts with the cyclic 32-state W9 chamber.

Primary questions:

```text
does W10 contain depth 11?
does the unit-slope edge law persist?
does the height range remain consecutive?
```


### OBS-018 — Constraint Edge Sectorizes the W9 State Chamber

Status: recorded on 2026-09-30.

Files:

```text
python/Tromino/experiments/OBS-018-ConstraintEdgeSectorization/
  README.md
  summary.json
```

The complete W10 chamber has four states and three edges with depth labels
`9,9,10,9`; no depth-eleven state appears.

More strongly, its four state projections and all three transition edges occur
verbatim as the induced W9 subgraph on parent states:

```text
8 -- 14 -- 12 -- 10
9     9     10    9
```

The added edge `5-17` imposes `c5 != c17` at the blocker state. Among the
32 W9 states, exactly 16 satisfy this constraint, and they split into four
disconnected four-state sectors. The W10 restore state lands in sector
`{8,10,12,14}`.

Thus the observed 32 -> 4 contraction is explained as constraint-edge
sectorization plus connected-component selection, while first-exit depth is
preserved on the surviving shared sector.

### Next experiment — preserving-flip chamber census

The harness now provides:

```text
flip-chamber-census WITNESS
```

It scans every legal preserving one-flip neighbor of the W9 witness, restores
the same blocker step, enumerates the static proper + Missing-valid state
component, and compares that component with the complete W9 chamber.

The experiment records whether each child chamber:

```text
is a projection subset of W9
is an induced W9 subgraph
matches the sector predicted by the added-edge properness constraint
changes blocker adjacency
changes the restored blocker coloring
```

This is a cheap structural census before choosing additional neighbors for
full repair-depth evaluation.


### Flip chamber census correction before OBS-019

The first pushed `w9-flip-chamber-census-v24/summary.json` exposed a bug in
the **predictor-only** connected-component aggregation.

The queue traversal used a fixed `range(len(queue))`, so newly appended
vertices were marked seen but not traversed. This corrupted:

```text
parent_filtered_components
predicted_parent_sector
predicted_sector_match_count
```

It did **not** affect the independently enumerated child chamber files,
projection overlap counts, or induced-subgraph comparison.

The harness has been fixed and strengthened. The corrected census now also
tests every W9 projection directly in the full child restore context
(child graph + fixed prefix colors + Missing invariant), then compares the
child chamber against the connected sector containing the child baseline.

A local recomputation from the already pushed child chamber files predicts:

```text
exact child-admissible sector matches:
neighbors 1, 3, 11, 13, 14, 16
count = 6 / 17
```

Rerun the census before freezing OBS-019.


### OBS-019 — Six Exact Child-Admissible Sectors

Status: recorded on 2026-09-30.

Corrected one-flip census:

```text
legal preserving neighbors           = 17
child projection subsets of W9       = 6
induced subgraph matches              = 6
exact child-admissible sector matches = 6
simple added-edge predictor matches   = 5
```

Exact sector indices:

```text
1, 3, 11, 13, 14, 16
```

The full child-context admissibility predicate is the correct abstraction.
Neighbor 16 is the counterexample to an added-edge-only predictor.

### Next experiment — sector height census

New script:

```text
python/Tromino/search/sector_height_census.py
```

It evaluates repair height on every state of the six exact sectors and compares
each child state with its matched W9 state.

Targets:

```text
height-label preservation
edge |delta h|
depth 11
repair-maze volume
```
