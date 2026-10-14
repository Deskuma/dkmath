# instruction-004 — shared-coordinate state projection / chamber transport

## Role

Checkpoint 001–003 are complete with Outcome A.

This checkpoint formalizes the transport pattern used by OBS-019/020:

```text
child/parent topology may differ
but both expose the same mutable-coordinate state
and the child chamber projects to one parent admissible sector.
```

Do not prove that arbitrary Tromino flips satisfy these hypotheses.

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     dev/Tromino-RepairHeight-Sectorization-260930-v0
base:       develop
```

Read first:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/README.md
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/ROADMAP.md
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-003.md
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md
python/Tromino/experiments/OBS-020-UnitSlopeStructural/README.md
python/Tromino/search/sector_height_census.py
```

Inspect:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
DkMath/Tromino/RepairChamber.lean
```

## Task 1 — generic transport module

Create:

```text
DkMath/Tromino/StateProjectionTransport.lean
```

Use arbitrary types:

```lean
Child : Type*
Parent : Type*
```

with:

```text
childStep        : Child -> Child -> Prop
parentStep       : Parent -> Parent -> Prop
parentAdmissible : Parent -> Prop
project          : Child -> Parent
childRoot        : Child
parentRoot       : Parent
```

Keep this section independent of SimpleGraph.

## Task 2 — rooted transport packet

Define a small structure, preferably `RootedChamberTransport`, carrying:

```text
project_injective:
  Function.Injective project

root_project:
  project childRoot = parentRoot

parent_root_admissible:
  parentAdmissible parentRoot

map_step:
  childStep c d
  -> Restricted parentStep parentAdmissible (project c) (project d)

lift_step:
  Restricted parentStep parentAdmissible (project c) p
  -> exists d, childStep c d and project d = p
```

Interpretation:

```text
map_step  = every child edge projects to an admissible parent edge;
lift_step = the projected child image is locally closed under admissible
            parent edges;
injective = one projection key identifies at most one child state.
```

No Finset enumeration, cardinality theorem, or BFS.

## Task 3 — path mapping

Using `Steps`, prove:

```text
Steps childStep n c d
->
Steps (Restricted parentStep parentAdmissible) n
  (project c) (project d).
```

Preserve exact length.

## Task 4 — path lifting

Using `lift_step`, prove:

```text
project c = p0
Steps (Restricted parentStep parentAdmissible) n p0 p
->
exists d,
  Steps childStep n c d
  and project d = p.
```

Zero-step must return `c`; successor/prepend must lift one edge and recurse.

## Task 5 — exact chamber transport

Prove the central theorem:

```text
Reachable childStep childRoot c
<->
AdmissibleChamber parentStep parentAdmissible
  parentRoot (project c).
```

Forward: map the child path.

Reverse:

```text
parent chamber path to project c
-> lift to some child d
-> project d = project c
-> injectivity gives d = c.
```

Also expose the image theorem if clean:

```text
AdmissibleChamber parentStep parentAdmissible parentRoot p
<->
exists c, Reachable childStep childRoot c and project c = p.
```

This is the generic form of:

```text
projected child chamber
=
parent admissible sector containing the projected child baseline.
```

## Task 6 — induced-edge exactness

Derive:

```text
childStep c d
<->
Restricted parentStep parentAdmissible (project c) (project d).
```

The reverse direction should use `lift_step` and projection injectivity.

This theorem only concerns points in the projection image.

## Task 7 — common mutable-coordinate carrier

Add the Tromino-specific coordinate section.

For:

```lean
V : Type*
mutable : V -> Prop
```

define a graph-independent coordinate carrier:

```text
MutableCoordinates mutable
  := {v : V // mutable v} -> TrominoState
```

or an equivalent dependent-function type.

For ANY `G : SimpleGraph V`, define:

```text
mutableColorProjection G mutable
  : G.Coloring TrominoState -> MutableCoordinates mutable
```

by restriction to mutable vertices.

The codomain MUST NOT depend on `G`.

This permits parent and child graph colorings to be compared without coercing
one coloring type into the other.

## Task 8 — fixed-context injectivity

Projection to mutable coordinates is not injective on arbitrary full
colorings. Make the fixed outside context explicit.

Suggested predicate:

```text
AgreesOutside mutable base c
  := forall v, not mutable v -> c v = base v
```

where `base : V -> TrominoState` is graph-independent.

Prove, for two colorings of the SAME graph:

```text
AgreesOutside mutable base source
AgreesOutside mutable base target
mutableColorProjection ... source = mutableColorProjection ... target
-> source = target.
```

Optionally package a subtype such as `FixedContextColoring` and prove the
projection is injective on that subtype.

Do not require `base` itself to be a valid coloring.

This models the Python rule:

```text
full state = fixed restore-prefix context + mutable projection.
```

## Task 9 — cross-graph projection comparison

For:

```lean
Gparent Gchild : SimpleGraph V
```

define a small predicate such as:

```text
SameMutableProjection mutable parentColoring childColoring
```

and prove:

```text
SameMutableProjection ...
<->
forall v, mutable v -> parentColoring v = childColoring v.
```

Do not coerce child coloring to parent coloring.

## Task 10 — regression

Add:

```text
DkMathTest/Tromino/StateProjectionTransportRegression.lean
```

Regression A — abstract sector transport:

```text
small Child and Parent types;
parent has an extra admissible component;
projection image is exactly the root component;
map_step / lift_step / injectivity hold;
verify chamber iff and induced-edge iff.
```

Regression B — shared coloring coordinates:

```text
two different tiny SimpleGraphs on the same vertex type;
proper TrominoState colorings;
both project into exactly the same MutableCoordinates type;
SameMutableProjection works;
fixed-context injectivity works on one graph.
```

Do not encode W9.

## Task 11 — axiom audit

Add:

```text
DkMathTest/Tromino/StateProjectionTransportAxiomAudit.lean
```

Audit:

```text
path mapping
path lifting
projected chamber equivalence
child-chamber image theorem
induced-edge iff
fixed-context projection injectivity
```

No new axiom declarations.

## Non-goals

Do not implement or claim:

```text
a concrete flip-generated transport provider
a concrete Python Missing-Color invariant
every preserving flip has shared mutable coordinates
every child projection lies in the parent component
every preserving flip is transport-compatible
cross-topology repair-height monotonicity
childHeight <= parentHeight
height-label preservation
the six OBS-019 sectors as a universal theorem
Four Color Theorem
```

Do not modify the Port triangulation/reduction chain.

## Validation

From `lean/dk_math` run:

```text
lake build DkMath.Tromino.StateProjectionTransport
lake build DkMathTest.Tromino.StateProjectionTransportRegression
lake build DkMathTest.Tromino.StateProjectionTransportAxiomAudit
lake build DkMath.Tromino.StateSector
lake build DkMath.Tromino.RepairChamber
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
unsafe
```

Record warnings separately from build failures.

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-004.md
```

Record:

```text
Outcome A / B / C
files changed
transport packet representation
path-map theorem
path-lift theorem
projected chamber equivalence
child chamber image theorem
induced-edge theorem
MutableCoordinates representation
mutableColorProjection
fixed-context API
projection injectivity theorem
SameMutableProjection API
regression results
axiom audit
build results
git diff --check
forbidden-token scan
deviations
requirements remaining for a concrete OBS-019 flip provider
```

Outcome A:

```text
generic exact rooted chamber transport is production-proved;
shared mutable-coordinate projection across different graph colorings is
production-defined;
fixed-context injectivity is proved;
the next checkpoint may investigate a concrete flip/Missing-valid provider.
```

Outcome B:

```text
one of the two halves (generic chamber transport / graph-color coordinate
bridge) is complete but the other needs API repair; preserve the completed
half and report the exact obstruction.
```

Outcome C:

```text
the local edge-lifting contract is insufficient for exact chamber transport;
report the counterexample or missing hypothesis instead of adding unjustified
global assumptions.
```
