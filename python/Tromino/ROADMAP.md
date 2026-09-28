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
