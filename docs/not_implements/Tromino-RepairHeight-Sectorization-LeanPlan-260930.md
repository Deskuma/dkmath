# Tromino Repair Height / Sectorization Lean Formalization Plan — 2026-09-30

## Status

Research branch:

```text
research/Tromino-EisensteinTexture-Simulation-260928-v0
```

Evidence frozen through:

```text
OBS-019 — Six Exact Child-Admissible Sectors
OBS-020 — Unit-Slope Is Structural
```

This document marks the point where the structural layer is mature enough to
move into Lean.

It does **not** promote the empirical Four Color program, cross-topology height
monotonicity, or any universal coloring claim.

## 1. Experimental facts that motivate formalization

For the W9 blocker chamber:

```text
32 states
48 one-point recoloring edges
repair height values 8,9,10
all 48 edges satisfy |delta h| <= 1
```

For the six exact child-admissible sectors selected by preserving flips:

```text
98 child-state evaluations
all six child graphs satisfy |delta h| <= 1
only 21 / 98 child heights equal the matched W9 height
77 / 98 are lower
0 / 98 are higher
```

Thus cross-topology height preservation is false, while local unit slope is
stable across all tested fixed topologies.

A direct audit also confirms:

```text
every state-component edge differs at one unlocked vertex;
that vertex is a singleton Kempe component for the old/new color pair;
all 98 evaluated roots have no initial safe candidate.
```

## 2. Structural explanation

The Python observable should be separated into two graph layers.

### 2.1 Repair move graph

For one fixed topology / blocker / remaining set / policy:

```text
vertices = colored repair states
edges    = one Kempe exchange
Exit(s)  = s has a safe candidate for the current blocker
```

Kempe exchange is involutive, so the repair relation is symmetric.

For a blocked state `s`:

```text
repairHeight(s)
  = shortest number of repair edges from s to Exit.
```

Therefore repair height is graph distance to a fixed target set.

Distance to a target set in an undirected graph is 1-Lipschitz along graph
edges.

### 2.2 Admissible one-point state graph

The finite chamber experiments use another relation:

```text
s -- t
iff
s and t are proper + Missing-valid,
and differ at exactly one unlocked colored vertex.
```

If the old color is `a` and the new color is `b`, properness of both endpoint
colorings implies the changed vertex has no neighbor colored `a` or `b`.
Hence it is the singleton Kempe component `{v}` for the pair `{a,b}`.

Therefore every admissible one-point state edge is also one repair-move edge.

This is the bridge that turns the general distance theorem into the observed
unit-slope theorem.

## 3. First Lean target: generic repair-distance kernel

Do not begin with the concrete planar/Tromino coloring structure.

Start with a generic symmetric transition relation.

Suggested new module:

```text
lean/dk_math/DkMath/Tromino/RepairDistance.lean
```

A minimal abstract interface is enough:

```text
State : Type*
step  : State -> State -> Prop
exit  : State -> Prop

hsymm : Symmetric step
```

Avoid depending on finiteness if possible.

### 3.1 Exact-length path relation

A small local inductive relation can avoid uncertain Mathlib distance APIs.

Conceptual shape:

```text
Steps step n x y
```

with:

```text
Steps step 0 x x
step x y -> Steps step n y z -> Steps step (n+1) x z
```

Required lemmas:

```text
Steps.prepend
Steps.reverse_of_symmetric
Steps.add / concat
```

### 3.2 Exit reachability and height

Define:

```text
CanExitAt step exit n x :=
  exists y, exit y and Steps step n x y
```

For a state with a reachable exit:

```text
repairHeight x := Nat.find (exists n, CanExitAt step exit n x)
```

Do not silently assign a natural height to unreachable states.

Either:

```text
repairHeight (hreachable : exists n, ...)
```

or define an extended/optional height in a later layer.

Required correctness lemmas:

```text
repairHeight_spec
repairHeight_minimal
```

### 3.3 Unit-slope theorem

Core theorem:

```text
step x y ->
repairHeight x <= repairHeight y + 1
```

under exit-reachability assumptions.

Use symmetry for the reverse inequality.

Public theorem should preferably expose:

```text
step x y ->
repairHeight x <= repairHeight y + 1
and
repairHeight y <= repairHeight x + 1
```

Optionally derive:

```text
Nat.dist (repairHeight x) (repairHeight y) <= 1
```

if the relevant Mathlib API is stable.

This theorem is independent of Tromino geometry.

## 4. Second Lean target: restriction / sectorization kernel

Suggested module:

```text
lean/dk_math/DkMath/Tromino/StateSector.lean
```

For a parent relation `R` and child-admissibility predicate `A`, define the
restricted relation:

```text
Restricted R A x y :=
  A x and A y and R x y
```

Define the chamber rooted at `root` by reflexive-transitive reachability in
that restricted relation.

Core theorem:

```text
if childStep x y <-> Restricted parentStep childAdmissible x y,
then the child chamber rooted at childRoot
equals the connected/reachable component of the parent relation restricted
to childAdmissible that contains childRoot.
```

This formalizes the structural content of OBS-019.

Do not encode the experimental number six or the 32-state W9 witness in the
generic theorem.

## 5. Third Lean target: one-point recolor -> singleton Kempe move

This needs a concrete graph-coloring layer and should come after the generic
kernels compile.

Suggested module:

```text
lean/dk_math/DkMath/Tromino/KempeRepair.lean
```

Possible data:

```text
G      : SimpleGraph V
color  : V -> TrominoState
locked : Set V
```

Define properness using graph adjacency.

For colors `a,b`, define the induced two-color support:

```text
{v | color v = a or color v = b}
```

and its connected components.

Target lemma:

```text
source proper
target proper
source and target differ only at unlocked v
source v = a
target v = b
a != b
-----------------------------------------------
{v} is the source (a,b)-Kempe component containing v
```

Corollary:

```text
proper one-point recolor is a legal singleton Kempe exchange
```

Then combine it with `RepairDistance` to obtain the Tromino-facing
unit-slope theorem.

## 6. Important implementation boundary

The Python helper `repair_maze_from_explicit_state` records first exits only
after at least one repair move.

The mathematical Lean definition should use the natural convention:

```text
if the root already has a safe candidate, repairHeight = 0.
```

The OBS-020 calibration states are all genuinely blocked, so this convention
does not alter those 98 measurements.

Do not reproduce the Python implementation artifact as the mathematical
definition.

## 7. Claims that must remain outside the theorem layer

Do not state or imply:

```text
childHeight <= parentHeight for every preserving flip
height labels are preserved by sectorization
all preserving flips are transport-compatible
repair heights always lie in three consecutive levels
the experimental algorithm proves the Four Color Theorem
```

The 98-state census actually disproves general cross-topology height
preservation in the tested family.

## 8. Suggested implementation order

1. `RepairDistance.lean`
   - exact-length paths
   - minimum exit distance
   - unit-slope theorem

2. `StateSector.lean`
   - predicate restriction
   - rooted chamber
   - sectorization theorem

3. tests / finite calibration
   - tiny path graph with heights 0,1,2
   - restricted graph splitting into sectors

4. `KempeRepair.lean`
   - proper coloring definitions
   - two-color component
   - singleton recolor bridge

5. connect to existing:
   - `DkMath.Tromino.State`
   - `DkMath.Tromino.Exchange`
   - `DkMath.Tromino.GraphColoringBridge`

## 9. Acceptance criteria

For the first PR:

```text
lake build succeeds
no sorry
no new axioms beyond normal Mathlib kernel dependencies
generic unit-slope theorem is proved
generic sectorization theorem is proved
finite regression examples compile
no Four Color endpoint claim
```

The concrete Kempe bridge may be a second PR if it substantially increases the
scope.
