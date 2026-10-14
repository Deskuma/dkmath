# Tromino Eisenstein Texture Simulation

This directory is the Python experiment space for the Tromino / four-state
coloring research.

The immediate goal is not to prove the Four Color Theorem in Python.  The goal
is to turn the current Tromino ideas into a reproducible finite-state puzzle,
measure where local exchange succeeds or fails, and extract invariants that can
later be formalized in Lean.

## Research pipeline

The working direction is

```text
abstract embedded data structure
    -> color-index puzzle
    -> Trigon macro map
    -> Eisenstein texture overlay
    -> white-map style rendering
    -> theorem candidates for Lean
```

Small exploratory calculations may be done interactively.  Once an experiment
is informative, its generator, seed, solver configuration, result data, figures,
and analysis should be fixed in this directory so that the observation is
reproducible.

## Core state model

Use the four Tromino states

```text
V4 = {0, A, B, C}
```

with the intended additive interpretation
`V4 ~= ZMod 2 x ZMod 2`.

For an abstract region-adjacency structure `G = (V, E)`, a valid coloring
satisfies

```text
color(u) != color(v)
```

for every adjacency edge `u-v`.

The embedded data structure must retain more than graph adjacency.  In
particular, the cyclic order of neighbors around a node is part of the input
because later Trigon realization must preserve planar incidence information.

A minimal experimental node therefore carries:

- a stable node identifier,
- a color index in `{0, A, B, C}`,
- adjacency,
- cyclic neighbor order,
- optional boundary / outer-face metadata,
- optional texture coordinate / phase metadata.

## Texture interpretation

The Eisenstein texture is treated first as a baseline state field, not as a
completed proof of a map coloring.

For a representative point `b(v)` of a macro region, let

```text
texture(v) = T(b(v))
```

be the initial color index read from the periodic texture.

A later local correction may be represented by a phase value `phi(v)`, with

```text
color(v) = texture(v) + phi(v)
```

in the four-state group.

The current hypothesis is that GapSwap / local exchange can act as a phase
correction mechanism when the raw texture produces adjacency conflicts.

## Boundary / outer-sea convention

One important experiment fixes an outer sea state to `0`.

Then boundary regions must avoid `0`, so their visible palette is constrained
to

```text
{A, B, C}
```

The simple target pattern is alternating `A/B` on ordinary boundary runs and
using `C` as a repair state when parity or local adjacency requires it.

This is an experimental boundary condition, not yet a theorem asserting that a
particular GapSwap strategy always succeeds.

## High-degree regions and Trigon normalization

A single flat Eisenstein site has six natural neighboring directions, but an
abstract map region may have degree greater than six.

The proposed normalization does not discard the original region.  Instead, a
high-degree region is expanded into a connected triangular macro patch with:

- one macro-region identity,
- one representative point,
- enough boundary ports for all neighbors,
- the original cyclic neighbor order preserved.

A self-similar triangular expansion with side scale `2^k` gives boundary
capacity

```text
3 * 2^k
```

so the smallest level satisfying

```text
degree(v) <= 3 * 2^k
```

is a candidate normalization rule.

The macro region still has one color index; its micro-triangles are geometric
support for ports and texture, not separate original map regions.

## Solver architecture

Python experiments should keep an exact reference solver separate from the
heuristic exchange solver.

The reference solver answers whether a small generated instance has a valid
four-state coloring.  The GapSwap solver is then evaluated against that oracle.

A heuristic failure is therefore useful data:

- if the exact solver succeeds but GapSwap stalls, the failure exposes a gap in
  the move set or strategy;
- if both fail, inspect the generator and embedding assumptions before drawing
  conclusions.

The first optimization target is not minimal swap count.  First determine
whether the selected local moves can reach a valid state at all.

## Reproducible experiment records

Every nontrivial experiment promoted from scratch work should record at least:

- generator version,
- random seed,
- number of nodes and edges,
- degree statistics,
- boundary size and boundary convention,
- initial conflict count,
- move strategy,
- swap / backtrack count,
- success or failure,
- smallest failure witness when available,
- exact-oracle result,
- generated figures if useful.

Suggested layout:

```text
python/Tromino/
  README.md
  ROADMAP.md
  model.py
  generator.py
  oracle.py
  gapswap.py
  texture.py
  trigon.py
  render.py
  experiment.py
  tests/
  experiments/
  results/
```

The implementation instruction for Codex is intentionally deferred until the
initial scratch experiments have fixed the first move set and measurable
questions.

## Relation to Lean

Python is an exploratory and diagnostic layer.

When repeated experiments expose a stable invariant, the next step is to state
that invariant independently of the simulation and formalize it in the existing
`DkMath.Tromino` Lean development.

The current Lean reduction spine already isolates the all-triangular
genus-zero tetrahedral target.  This Python work is intended to investigate a
constructive route toward that remaining target, not to replace kernel-checked
proof.
