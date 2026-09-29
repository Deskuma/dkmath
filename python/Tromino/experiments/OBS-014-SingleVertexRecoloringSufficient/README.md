# OBS-014 — Single Vertex Recoloring Is Sufficient

Date: 2026-09-30

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-014 freezes the partial blocker-state intervention experiment following
OBS-013.

The parent W9 graph is held fixed at blocker node `19` / restore step `16`.
The only parent-to-child blocker-state differences are:

```text
vertex 4 : 1 -> 0
vertex 17: 3 -> 1
```

All subsets of those state changes were evaluated.

## Source

Directory:

```text
python/Tromino/results/repair-depth/w9-w10-state-subsets-v24/
```

Files:

```text
subset-none.json
subset-4.json
subset-17.json
subset-4-17.json
summary.json
```

## Complete subset result

```text
{}:
  valid
  first exit depth = 9
  depth-9 exits    = 2
  depth-10 exits   = 4

{4}:
  valid
  first exit depth = 10
  depth-9 exits    = 0
  depth-10 exits   = 4

{17}:
  invalid
  edge 4-17 becomes monochromatic color 1

{4,17}:
  valid
  first exit depth = 10
  depth-9 exits    = 0
  depth-10 exits   = 4
```

Therefore the unique minimal valid raising subset is:

```text
{4}
```

and the single recoloring

```text
vertex 4 : 1 -> 0
```

is sufficient, on the fixed parent topology, to reproduce the depth-nine to
depth-ten shift.

## Correction to the earlier component-fusion picture

OBS-012 identified a common (0,1) component enlargement in the full child
blocker state.

The subset experiment shows that this full-child fusion is **not necessary**
for the depth jump.

Under the single-vertex intervention `4:1->0`, the initial parent (0,1)
components

```text
{4}
{8,9,10,11,12,15}
{14}
```

remain separated, yet the first exit still moves from depth nine to depth ten.

Thus the full-child component fusion is a real downstream feature, but not the
minimal causal mechanism.

## How the one-vertex change kills the two parent exits

The two parent depth-nine paths are affected differently by the same recolored
vertex.

### Parent exit 0

All nine parent Kempe moves remain exactly available under the `{4}`
intervention.

However, after those nine moves the parent has blocker-neighbor palette:

```text
{1,2,3}
```

so candidate color `0` becomes available.

With `vertex 4 = 0`, the same nine moves leave vertex 4 as a color-zero
neighbor of blocker node 19. The blocker palette remains:

```text
{0,1,2,3}
```

and candidate `0` never opens.

So exit 0 is destroyed by **target-color occupancy**, not by loss of its path.

### Parent exit 1

The second parent path remains exact through four moves.

At its fifth move the parent requires a (1,3) component containing:

```text
{3,4,5,6,10,13,14,15,17,18}
```

but recoloring vertex 4 from 1 to 0 removes vertex 4 from that color pair and
splits the required parent component.

So exit 1 is destroyed by a later **Kempe-component restructuring**.

## Minimal mechanism for this witness

The current smallest successful intervention is therefore:

```text
one colored neighbor of the blocker
vertex 4
changes from color 1 to the desired exit color 0
```

and that single state change destroys both shallow exits by two different
mechanisms.

The causal chain has now been reduced to:

```text
diagonal flip
-> earlier repair
-> vertex 4 recolored 1 -> 0
-> shallow exit 0 blocked by persistent target-color occupancy
-> shallow exit 1 blocked by later component restructuring
-> first exit depth 9 -> 10
```

## What OBS-014 does not establish

It does not establish:

- that vertex 4 is the only blocker neighbor whose recoloring to color 0 raises
  repair depth;
- that target-color pinning is sufficient in other witnesses;
- that every depth increase can be reduced to one vertex;
- a monotone or Collatz-like recurrence;
- any Four Color Theorem consequence;
- any Lean theorem.

## Next experiment

Keep the parent W9 graph and blocker state fixed.

For every unlocked colored neighbor of blocker node 19, recolor that one
neighbor to target exit color `0`, when the resulting partial coloring is
proper and satisfies the Missing-Color invariant.

Measure:

```text
validity
first exit depth
depth-9 exit count
depth-10 exit count
maze size
whether the pinned vertex occurs in either parent depth-nine repair path
```

The key question is whether vertex 4 is unique among blocker-neighbor
target-color pins, or whether a larger class of one-point pinning operations
raises the repair depth.
