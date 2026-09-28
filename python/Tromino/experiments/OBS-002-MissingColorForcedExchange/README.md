# OBS-002 — Missing-Color Invariant with Forced Local Exchange

Date: 2026-09-28

Branch:

~~~
research/Tromino-EisensteinTexture-Simulation-260928-v0
~~~

## Purpose

This observation records the next scratch experiment after OBS-001.

OBS-001 showed that a legal local color choice can destroy the future missing
fourth color and create a later dead end. OBS-002 therefore changes the solver:

1. preserve the Missing-Color Invariant whenever a direct color choice can do so;
2. do not exchange colors while a direct invariant-preserving choice exists;
3. when every direct choice would violate the invariant, search for a small
   local color exchange;
4. measure the exchange depth actually required.

The experiment is still diagnostic. The exchange move used here is a
two-color Kempe-component swap used as a proxy for a future DkMath GapSwap
implementation. This report does not identify the proxy move with the formal
Tromino exchange law.

## Model

The random planar input generator is the same family used by OBS-001:

1. sample n points uniformly in the unit square;
2. compute the Delaunay triangulation;
3. add an outer-sea node;
4. connect the sea to all convex-hull vertices;
5. fix the sea color to 0.

Colors are {0,1,2,3}, with 0 reserved for the sea.

A degree-4 peel is performed and then reversed. All recorded instances in this
run had empty 4-core, so every land node was restored from the sea boundary.

For a not-yet-restored node w, define

~~~
P(w) = { color(u) | u is already restored and u ~ w }.
~~~

The working invariant is

~~~
|P(w)| <= 3.
~~~

A direct candidate color for the current restore node is admissible only if the
candidate remains different from all already-colored neighbors and leaves the
Missing-Color Invariant true for every future node.

## Forced exchange rule

If at least one direct invariant-preserving color exists, the solver colors the
node directly.

Only when no direct choice is safe does it search for an exchange.

The exchange proxy is:

- choose two colors a,b;
- take one connected component of the already-colored subgraph induced by
  colors a,b;
- swap a <-> b on that component;
- reject any component containing the sea;
- reject any intermediate state that violates the Missing-Color Invariant.

Exchange states are searched breadth-first up to a configured depth.

Thus repair depth means:

~~~
0  direct coloring only
1  at most one Kempe-component exchange before the color
2  at most two exchanges
3  at most three exchanges
~~~

This is a local-repair search, not full coloring backtracking.

## Reproduction environment

The frozen scratch run used:

~~~
Python 3.13.5
NumPy 2.3.5
SciPy 1.17.0
~~~

Reference script: scratch_obs002.py

Machine-readable results: summary.json

## Observation A — invariant preservation alone is insufficient

The direct-only solver already performs better than the plain greedy baseline
because it refuses choices that immediately destroy a future missing color.

Nevertheless its success rate still falls rapidly:

| land nodes | trials | direct invariant-preserving lift |
| ---: | ---: | ---: |
| 20 | 100 | 40 / 100 |
| 50 | 100 | 12 / 100 |
| 100 | 100 | 0 / 100 |
| 200 | 50 | 0 / 50 |

So the Missing-Color Invariant is useful as a branch filter but does not by
itself remove the need for repair.

## Observation B — one forced exchange resolves most stalls

Using at most one exchange when direct lifting is forced to stop:

| land nodes | trials | depth <= 1 success |
| ---: | ---: | ---: |
| 20 | 100 | 94 / 100 |
| 50 | 100 | 91 / 100 |
| 100 | 100 | 88 / 100 |
| 200 | 50 | 40 / 50 |
| 500 | 50 | 23 / 50 |

Mean repair events among successful depth-1 runs:

~~~
n=20   : 0.85
n=50   : 2.31
n=100  : 4.22
n=200  : 8.10
n=500  : 21.09
~~~

Most restore steps remain direct; exchange is invoked only at a sparse subset
of steps.

## Observation C — depth 2 is very strong, but not universally sufficient in this sample

For the first four size groups, depth two solved every recorded instance:

| land nodes | trials | depth <= 2 success | mean repair events |
| ---: | ---: | ---: | ---: |
| 20 | 100 | 100 / 100 | 0.94 |
| 50 | 100 | 100 / 100 | 2.35 |
| 100 | 100 | 100 / 100 | 4.37 |
| 200 | 50 | 50 / 50 | 8.46 |

A dedicated 500-node run was more informative:

| land nodes | trials | depth <= 2 success | mean repair events among successes |
| ---: | ---: | ---: | ---: |
| 500 | 50 | 49 / 50 | 22.35 |

So a provisional chat-side impression that depth two might always suffice was
too optimistic. The frozen rerun found an explicit depth-two failure.

## Observation D — explicit depth-3 witness

Seed 5200005, with 500 land nodes.

At restore step 427, current node 191 has no direct invariant-preserving color.

The depth-two exchange search also fails.

A depth-three search succeeds with the following exchange sequence before
assigning color 1 to node 191:

~~~
swap 0 <-> 1 on component
{60, 123, 139, 274, 483}

swap 2 <-> 3 on component
{23, 26, 58, 84, 89, 91, 127, 134, 154, 155, 212, 244,
 259, 261, 265, 297, 300, 305, 327, 333, 346, 351, 371, 372,
 385, 414, 432, 433, 438, 452, 458}

swap 1 <-> 2 on component
{11, 49, 74, 76, 81, 91, 97, 113, 123, 138, 164, 176, 203,
 208, 211, 216, 231, 237, 241, 261, 268, 271, 280, 282, 287,
 300, 311, 312, 343, 352, 361, 388, 416, 430, 452, 459, 473,
 496, 498}
~~~

The complete depth-3 run for this seed used 19 repair events, 21 exchange moves
total, and maximum repair depth 3.

This is the first frozen witness that the local maze can require more than two
exchange layers under the current proxy move set and deterministic lift order.

## Observation E — depth 3 solved the recorded 500-node batch

For seeds 5200000 through 5200049:

| maximum repair depth | success |
| ---: | ---: |
| 1 | 23 / 50 |
| 2 | 49 / 50 |
| 3 | 50 / 50 |

Mean repair events for the depth-3 solver: 22.28.

The maximum depth actually used in the batch was exactly 3.

This is an observation about this generator, ordering, and exchange proxy only.
It is not evidence that depth three is a universal bound.

## Maze interpretation

A direct invariant-preserving color is an open forward corridor.

A state with no direct safe color is a local wall.

A one-component exchange rewires the wall once.

Depth two or three means that several local rewrites must be composed before an
open corridor reappears.

The global map may contain hundreds of nodes while the obstruction is detected
at one restore step. This suggests that global problem size and local repair
depth are distinct quantities worth measuring separately.

The key function for later experiments is therefore

~~~
D(n) = maximum repair depth observed at size n
~~~

together with repair frequency.

## Relation to the quantum-computing question

OBS-002 weakens the naive argument that a huge coloring search tree by itself
makes the problem quantum-favorable.

A structural invariant plus targeted local exchange collapses much of the
observed search into shallow repairs.

The relevant question is now whether adversarial planar instances can force
repair depth to grow substantially with n, not merely whether the total number
of possible colorings grows exponentially.

No quantum advantage is claimed by this observation.

## What is established only as observation

Recorded for the specified random family and deterministic solver:

- direct Missing-Color preservation alone eventually stalls;
- one local exchange removes most stalls;
- depth two solved all recorded instances up to 200 nodes;
- depth two failed on at least one 500-node instance;
- depth three solved all 50 instances in the dedicated 500-node batch;
- seed 5200005 is an explicit depth-three witness.

Not established:

- that Kempe-component swaps are the final DkMath GapSwap move set;
- that every planar instance has empty 4-core under this peeling scheme;
- that depth three is a universal or asymptotic bound;
- that repair frequency is asymptotically linear;
- that the observed behavior extends to adversarial triangulations;
- any complexity or quantum-advantage theorem;
- any Lean theorem.

## Next experiment

The next experiment should become adversarial rather than merely larger.

Starting from a known solvable / planted tetrahedral configuration, add
controlled refinements or legal edge modifications one at a time and measure:

~~~
branch count
dead-end count
repair frequency
maximum repair depth
~~~

The target is to find the smallest explicit instance requiring depth four, or
to discover a structural reason why the present move set cannot create one.

That experiment should also distinguish growth caused only by increased
resolution, changed adjacency / rotation structure, and the chosen restore
order.
