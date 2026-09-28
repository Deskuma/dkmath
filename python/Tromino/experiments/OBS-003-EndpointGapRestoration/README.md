# OBS-003 — Endpoint Gap Restoration

Date: 2026-09-29

Branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

## Purpose

OBS-003 records the first clear separation between two ways of enforcing the
Missing-Color condition during local repair.

The original strict policy required

```text
|P(v)| <= 3
```

for every not-yet-restored node after every primitive exchange.

The endpoint policy relaxes only the intermediate repair states:

- the repair starts from a state satisfying the Missing-Color condition;
- intermediate primitive exchanges may temporarily violate it;
- the repair is accepted only when it reaches a state that restores the
  Missing-Color condition and permits the current vertex to be colored.

This observation does **not** prove that endpoint preservation is universally
sufficient. It records that one witness classified as unreachable under the
strict policy becomes solvable under the endpoint policy.

## Source run

The source long-run experiment is:

```text
python/Tromino/results/repair-depth/d5-v24/
```

with configuration:

```text
vertices           = 24
jobs               = 2000
steps              = 2000
warmup_flips       = 48
workers             = 8
max_depth          = 6
target_depth       = 5
node_limit         = 500000
base_seed          = 6000000
intermediate_policy= strict
```

The source summary recorded:

```text
jobs_completed      = 2000
resolved_jobs       = 160
max_resolved_depth  = 6
mean_resolved_depth = 5.1375
state_space_exhausted = 1840
target_found        = true
```

Because the search objective actively favors hard / unresolved states, these
counts are search-output counts, not estimates of natural frequencies over
planar maps.

## Observation A — strict depth 6 is a verified resolved witness

File:

```text
python/Tromino/results/repair-depth/d5-v24/best_resolved_witness.json
```

Seed:

```text
6000915
```

Replay:

```text
python/Tromino/results/repair-depth/d5-v24/replay-best-resolved.json
```

The strict-policy replay gives:

| depth ceiling | result |
| ---: | --- |
| 0 | forced repair |
| 1 | depth limited |
| 2 | depth limited |
| 3 | depth limited |
| 4 | depth limited |
| 5 | depth limited |
| 6 | solved |

At depth 5 the repair search for node `14`, restore step `11`, expands
`4734` states and remains depth-limited.

At depth 6 the same witness solves. The depth-6 repair at node `14` uses six
primitive component exchanges before assigning color `0`.

The successful strict run uses:

```text
repairs            = 5
repair_moves_total = 10
max_depth_used     = 6
required_depth     = 6
verified_against_depth_minus_one = true
```

Thus the current experimental family contains a verified strict repair-depth
six witness:

```text
D_strict(24) >= 6
```

This is an observation for the present generator, restore order, locked frame,
and Kempe-component exchange proxy.

## Observation B — a strict exhausted state is endpoint-solvable

File:

```text
python/Tromino/results/repair-depth/d5-v24/best_witness.json
```

Seed:

```text
6000596
```

Under the strict policy the long-run search records:

```text
classification   = state_space_exhausted
restore step     = 18
current node     = 21
repairs so far   = 7
expanded         = 23
hit_depth_limit  = false
search ceiling   = 6
```

The important point is `hit_depth_limit = false`: under the strict policy,
the reachable local repair state space was exhausted before the configured
depth ceiling became the blocker.

The endpoint replay is:

```text
python/Tromino/results/repair-depth/d5-v24/replay-endpoint.json
```

and gives:

| depth ceiling | endpoint result |
| ---: | --- |
| 0 | forced repair |
| 1 | depth limited |
| 2 | depth limited |
| 3 | solved |

The successful endpoint run uses:

```text
repairs            = 8
repair_moves_total = 12
max_depth_used     = 3
required_depth     = 3
verified_against_depth_minus_one = true
```

The final repair at node `21`, restore step `18`, has depth 3 and consists
of three successive `1 <-> 3` component exchanges before assigning color
`3`.

Therefore this witness is not evidence that the coloring itself is unreachable,
nor evidence that repair depth must exceed six. It is evidence that the strict
intermediate Missing-Color policy can exclude an exchange route that becomes
available when only the repair endpoint is required to restore the invariant.

## Structural interpretation

The experiment suggests distinguishing two notions.

### Strict Missing-Color repair

Every primitive exchange must remain inside the safe set:

```text
Safe(s_0), Safe(s_1), ..., Safe(s_k)
```

where `Safe` denotes the current Missing-Color condition.

### Endpoint Missing-Color repair

Only the repair boundary states must be safe:

```text
Safe(s_0)
s_0 -> s_1 -> ... -> s_(k-1) -> s_k
Safe(s_k)
```

Intermediate states may temporarily leave the safe set.

This motivates treating a Gap repair as a **composite repair path** rather than
requiring every primitive exchange to be individually Gap-preserving.

A candidate experimental formulation is:

```text
GapRepair(s, t) :=
  there exists a finite primitive-exchange path from s to t
  such that Safe(s) and Safe(t).
```

No claim is made yet that every required repair admits such a path.

## Two repair-depth observables

OBS-003 motivates separating:

```text
D_strict(G)
D_endpoint(G)
```

for the same graph, restore order, locked frame, and primitive move family.

The current data contain:

- a verified witness with `D_strict = 6` (seed `6000915`);
- a witness that is `state_space_exhausted` under strict repair but has
  `D_endpoint = 3` (seed `6000596`).

For strict-unreachable cases, the difference between the two depths is not a
finite numeric quantity, so it should not be forced into a scalar statistic
without an explicit convention.

## What OBS-003 establishes only as observation

Recorded:

- strict repair depth six occurs in the planted adversarial family;
- one strict exhausted witness becomes solvable with endpoint repair depth
  three;
- strict intermediate Missing-Color preservation can therefore be more
  restrictive than endpoint preservation;
- the current notion of GapSwap should remain separate from the
  Kempe-component proxy until the move law is analyzed directly.

Not established:

- that endpoint repair always succeeds;
- that endpoint repair depth is bounded by a constant;
- that the endpoint policy is the final DkMath GapSwap definition;
- that strict repair is mathematically incorrect rather than simply too
  restrictive for the intended algorithm;
- any Four Color Theorem consequence;
- any complexity-theoretic or quantum-advantage result;
- any Lean theorem.

## Next experiment

The next long-run campaign should make endpoint repair the primary policy and
search directly for large values of

```text
D_endpoint(G).
```

The immediate questions are:

1. can a verified endpoint depth 4, 5, 6, ... hierarchy be generated under the
   same planted wall-insertion process?
2. does endpoint depth grow with graph size or stay shallow?
3. when endpoint repair fails, is the blocker the Kempe proxy move family,
   the locked frame, the deterministic restore order, or a genuinely deeper
   local maze?
4. can the resulting composite repair path be expressed directly in the
   Tromino V4 exchange calculus?

The key conceptual change frozen by OBS-003 is:

> Missing Color need not be preserved by every primitive exchange; it may be a
> boundary condition of a composite repair.
