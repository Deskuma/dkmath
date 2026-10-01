# OBS-001 — Missing-Color Lift Scratch Observation

Date: 2026-09-28

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

This observation freezes the first chat-side Python experiment behind the
"missing fourth color" / outer-sea discussion.

It is not a proof of the Four Color Theorem, not a production solver, and not
yet the Codex implementation specification.

The question tested here is narrower:

> If a planar triangulated region structure is simplified and then restored,
> how quickly does a purely local coloring choice lose the missing fourth
> color, and does a heuristic that explicitly protects future missing colors
> delay that failure?

The experiment deliberately separates this lifting question from later
Eisenstein texture geometry and from an actual GapSwap move implementation.

## Model

Colors are represented as

```text
0, 1, 2, 3
```

with `0` used for the outer sea.

For each seed:

1. sample `n` random points uniformly in the unit square;
2. construct their Delaunay triangulation;
3. add one outer-sea node;
4. connect the sea to every convex-hull vertex.

The sea is permanently assigned color `0`.

A `k`-peel repeatedly removes a land node whose current degree is at most
`k`.  Restoration processes the removed nodes in reverse order.

For a restoring node `v`, define the current boundary palette

```text
P(v) = { color(u) | u is already restored and u ~ v }.
```

A restore step is immediately forced to fail if

```text
P(v) = {0, 1, 2, 3}.
```

This is the first concrete form of the proposed missing-color obstruction.

## Two greedy restore rules

### Plain greedy

Choose the least available color.

### Missing-color-aware greedy

For every currently available candidate color, inspect still-unrestored
neighbors and score the candidate lexicographically by:

1. how many future nodes would immediately see all four colors;
2. how many future nodes would see exactly three colors;
3. the sum of squared future palette sizes;
4. the numeric color index as a deterministic tie-break.

Choose the minimum score.

This is **not** yet GapSwap.  It is only a local branch-selection heuristic
designed to preserve a missing color for future restore steps.

## Reproduction environment

The frozen scratch run used:

```text
Python 3.13.5
NumPy 2.3.5
SciPy 1.17.0
```

The reference script is `scratch_obs001.py`.
The machine-readable output is `summary.json`.

## Observation A — degree 3 is safe but barely simplifies

For a node restored after a 3-peel, at most three already-restored neighbors
can constrain it.  Therefore at least one of the four colors is always absent.

In these random Delaunay samples, however, the 3-core was almost the entire
graph:

| land nodes | trials | mean 3-core | median 3-core |
| ---: | ---: | ---: | ---: |
| 20 | 100 | 19.50 | 20 |
| 50 | 100 | 48.89 | 49 |
| 100 | 100 | 98.25 | 98 |

So the completely forced / missing-color-safe regime does not provide much
simplification on this generator.

## Observation B — degree 4 is the first branching threshold

For all samples in this scratch run, the 4-peel removed every land node, so the
restore could begin from the fixed sea alone.

At degree four, however, a restoring node can see all four colors.  This is the
first local threshold where the missing color can disappear.

Greedy restore results:

| land nodes | trials | plain greedy | missing-color-aware |
| ---: | ---: | ---: | ---: |
| 20 | 100 | 15 / 100 | 30 / 100 |
| 50 | 100 | 2 / 100 | 12 / 100 |
| 100 | 100 | 0 / 100 | 1 / 100 |

The missing-color heuristic improves the success rate, but it does not remove
the obstruction.  The success rate still collapses as the instances grow.

This supports the interpretation that "preserve a missing color" is relevant,
but not sufficient as a complete local rule.

## Observation C — explicit branch-to-dead-end witness

Seed:

```text
120001
```

with 20 land nodes.

The first decision where the two restore rules differ occurs at node `17`.

Available colors:

```text
{1, 3}
```

Plain greedy chooses:

```text
1
```

Missing-color-aware greedy chooses:

```text
3
```

The plain branch later reaches node `16` with already-colored neighbors:

```text
node 18 -> 0
node 17 -> 1
node 13 -> 2
node  7 -> 3
```

Hence

```text
P(16) = {0, 1, 2, 3}
```

and no color remains.

The missing-color-aware branch for the same seed completes successfully.

This is the first frozen witness for the maze analogy:

```text
local branch
  -> one choice eventually fills all four boundary colors -> dead end
  -> another choice keeps a missing color                  -> success
```

The failure is therefore not caused by absence of a local choice at the earlier
branch point.  It is caused by choosing a branch that destroys a later missing
color.

## Observation D — backtracking exposes large search dispersion

The same missing-color score was used only to order branches in a depth-first
backtracking restore.

A search limit of 1,000,000 recursive states was imposed.

### 50 land nodes

All 10 seeds succeeded.

Search-node counts:

```text
19862, 776, 2820, 12958, 280,
4558, 9394, 248, 321181, 77
```

Median:

```text
3689
```

Maximum:

```text
321181
```

### 100 land nodes

3 of 10 seeds succeeded within the limit.

Search-node counts:

```text
1000055, 9091, 1000054, 1000051, 1000059,
1000047, 359, 1000045, 224584, 1000055
```

The values slightly above one million are the recursive call that detects the
limit crossing.

The large spread is an observation only.  It should not yet be labeled a
heavy-tail law or a quantum advantage.

## Candidate invariant

For every not-yet-restored node `v`, maintain

```text
|P(v)| <= 3.
```

Call this the **Missing-Color Invariant**.

If the invariant holds, every future node still has at least one color absent
from its already-restored boundary.

The next solver should therefore differ from the heuristic used here:

1. reject a candidate color if it would make some future palette size 4;
2. choose freely among invariant-preserving candidates;
3. invoke a genuine local GapSwap repair only when every direct candidate would
   violate the invariant;
4. record the smallest state in which such a forced repair is necessary.

This converts GapSwap from a general recoloring heuristic into a targeted
repair operator for imminent loss of the missing color.

## What this observation does and does not establish

Supported by this run:

- degree 3 is the local threshold at which a missing fourth color is automatic;
- allowing degree 4 introduces the first possible four-color boundary
  saturation;
- a future-palette-aware choice can avoid dead ends that plain greedy enters;
- the explicit seed `120001` records one such branch divergence;
- simple branch ordering alone still leaves rapidly growing search difficulty.

Not established:

- that the chosen random generator is representative of all planar maps;
- that every instance admits the proposed peel / lift strategy in the same
  form;
- that the Missing-Color Invariant can always be preserved;
- that GapSwap can always repair a forced violation;
- any complexity-theoretic or quantum-advantage claim;
- any Lean theorem.

## Next experiment

The next scratch experiment should implement

```text
invariant-preserving lift
    + forced GapSwap only when needed
```

and classify the first states where all direct restore choices would violate the
Missing-Color Invariant.

A second line of experiments should construct instances from a planted
tetrahedral / K4 solution and refine them while retaining the known solution
lineage.  That will separate "solution existence" from "the search lost the
solution branch".
