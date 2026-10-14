# instruction-005 — partial restoration state / Missing-valid kernel

## Role

Checkpoint 004 is complete with overall Outcome A.

This checkpoint formalizes the actual semantic state used by the Python
repair experiments before any concrete topology-changing flip provider is
attempted.

The crucial correction is:

```text
Python repair state = PARTIAL coloring.
```

`colored` vertices already carry colors. `remaining` vertices are still
uncolored. The existing Lean `G.Coloring TrominoState` is a total proper
coloring and therefore is not by itself the correct carrier for the
Missing-Color invariant.

Build the partial restoration layer and then bridge its already-colored
induced graph to the existing `KempeRepair` API.

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
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-004.md
python/Tromino/experiments/OBS-016-AdmissibleOnePointStateLandscape/README.md
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md
python/Tromino/experiments/OBS-020-UnitSlopeStructural/README.md
python/Tromino/search/repair_depth_search.py
```

Inspect:

```text
DkMath/Tromino/KempeRepair.lean
DkMath/Tromino/RepairChamber.lean
DkMath/Tromino/StateProjectionTransport.lean
```

## Task 1 — create production module

Create:

```text
DkMath/Tromino/RestorationRepairState.lean
```

Keep this module finite-search-free. No BFS, no witness IDs, no Python data.

## Task 2 — fixed restoration context

For a vertex type and graph:

```lean
V : Type*
G : SimpleGraph V
mutable : V -> Prop
```

define a small context structure carrying at least:

```text
colored   : V -> Prop
remaining : V -> Prop
base      : V -> TrominoState
mutable_colored : forall v, mutable v -> colored v
```

Prefer also an explicit disjointness field:

```text
remaining_uncolored : forall v, remaining v -> not colored v
```

if it matches the Python restoration state cleanly and simplifies later
statements.

Recommended structure name:

```text
RestorationContext G mutable
```

or another clear repository-style name.

`base` is only the fixed outside-mutable color context. Do NOT require it to
be a proper total coloring.

## Task 3 — coordinate state and realization

Reuse the checkpoint-004 carrier:

```text
MutableCoordinates mutable
```

as the restoration-state coordinate type.

Define realization into an ambient color assignment:

```text
realize context state : V -> TrominoState
```

with semantics:

```text
if mutable v
then use state at v
else use context.base v.
```

Prove:

```text
realize_mutable
realize_outside
```

and any extensionality lemma needed downstream.

This is the Lean form of:

```text
full colored dictionary = fixed restore-prefix context + mutable projection.
```

## Task 4 — properness only on colored vertices

Define partial-state properness:

```text
ProperOnColored G colored assignment
```

with semantics:

```text
for every graph edge u--v,
if colored u and colored v,
then assignment u != assignment v.
```

Do not test edges whose endpoint is still uncolored.

Define the context/state form:

```text
context.Proper state
```

or equivalent, using `realize`.

## Task 5 — Missing-Color invariant

The Python invariant is:

```text
for every w in remaining:
  number of colors seen among colored neighbors of w <= 3.
```

Because `TrominoState` has exactly four colors, formalize the equivalent
missing-color statement directly instead of building a counting API.

Define:

```text
MissingAt G colored assignment w
```

with semantics:

```text
exists missing : TrominoState,
  forall u,
    G.Adj u w ->
    colored u ->
    assignment u != missing.
```

Then:

```text
MissingValid G colored remaining assignment
  := forall w, remaining w -> MissingAt ... w.
```

and context/state form:

```text
context.MissingValid state.
```

This directly captures the intended four-color gate without requiring
`Fintype V`, palette cardinalities, or finite enumeration.

Do NOT claim any theorem about `safe_candidates` in this checkpoint.

## Task 6 — restoration admissibility

Define:

```text
RestorationAdmissible context state
```

as exactly:

```text
context.Proper state
and
context.MissingValid state.
```

This is the production abstraction of the Python static admissibility test:

```text
explicit_state_proper_violations == none
and
invariant_holds == true.
```

## Task 7 — one-coordinate transition

Define a graph-independent relation on mutable coordinate states:

```text
CoordinateOnePointStep mutable source target
```

with semantics:

```text
there exists one mutable coordinate v
such that source v != target v
and every other mutable coordinate is unchanged.
```

Because the carrier itself is indexed only by mutable vertices, the witness
may naturally be a subtype `{v // mutable v}`.

Prove:

```text
CoordinateOnePointStep is symmetric.
```

Then define the Python-style admissible state edge:

```text
AdmissibleRestorationStep context
  := Restricted (CoordinateOnePointStep mutable)
       (RestorationAdmissible context).
```

Prove symmetry via `restricted_symmetric`.

## Task 8 — colored induced graph

Define the already-colored vertex carrier:

```text
ColoredVertex context := {v : V // context.colored v}
```

and the simple graph induced from `G` on those vertices.

Use the exact Mathlib induced-subgraph API available in Lean 4.34. Inspect
signatures before committing to names.

From a state plus a proof of `context.Proper state`, construct a proper
`TrominoState` coloring of this colored induced graph.

Recommended theorem/definition semantics:

```text
partialColoring
  : context.Proper state
  -> ColoredGraph context .Coloring TrominoState.
```

Do not color remaining vertices in this object.

## Task 9 — mutable vertices inside the colored graph

Lift the mutable predicate to `ColoredVertex context`.

Because the context requires:

```text
mutable v -> colored v
```

every mutable original vertex has a canonical colored-vertex representative.

Provide the small conversion lemmas needed to move a one-coordinate witness
into the induced colored graph.

## Task 10 — bridge coordinate one-point change to existing OnePointRecolor

Let `source` and `target` be coordinate states with:

```text
CoordinateOnePointStep mutable source target
context.Proper source
context.Proper target.
```

Construct their induced-graph proper colorings and prove they satisfy the
existing:

```text
OnePointRecolor
```

on the colored induced graph with the lifted mutable predicate.

Required theorem semantics:

```text
CoordinateOnePointStep
+ proper source
+ proper target
-> OnePointRecolor inducedColoredGraph liftedMutable
     (partialColoring source)
     (partialColoring target).
```

Then derive by reuse, not re-proof:

```text
onePointRecolor_singletonKempeMove
```

that every admissible restoration edge gives a singleton Kempe move on the
already-colored induced graph.

Expose a theorem with semantics:

```text
AdmissibleRestorationStep context source target
->
SingletonKempeMove inducedColoredGraph liftedMutable
  (partialColoring source)
  (partialColoring target).
```

This is the sound partial-coloring version of OBS-020.

## Task 11 — same-coordinate parent/child context interface

For two contexts on the SAME vertex type and SAME mutable predicate but
possibly different graphs, colored sets, remaining sets, or base contexts:

```text
parentContext
childContext
```

their state carrier is definitionally the same:

```text
MutableCoordinates mutable.
```

Provide small helper predicates/theorems for:

```text
parent admissible state
child admissible state
parent-and-child admissible state.
```

Define:

```text
TransportAdmissible parent child state
  := parent.Admissible state and child.Admissible state.
```

or equivalent.

Show that:

```text
Restricted (CoordinateOnePointStep mutable)
  (TransportAdmissible parent child)
```

is exactly the parent coordinate state graph filtered by full child
admissibility.

This is the static predicate used by the corrected OBS-019 predictor.

Do NOT yet prove that a topology flip satisfies child-admissible ->
parent-admissible.

## Task 12 — finite regression

Add:

```text
DkMathTest/Tromino/RestorationRepairStateRegression.lean
```

Use a tiny graph with:

```text
some colored vertices,
at least one remaining uncolored vertex,
at least one mutable colored vertex.
```

Verify:

```text
1. realize uses mutable coordinates and fixed base correctly;
2. Proper ignores edges to uncolored vertices;
3. MissingAt holds when one TrominoState color is absent from colored
   neighbors;
4. MissingValid fails when four differently colored colored-neighbors are
   arranged around a remaining vertex;
5. a proper + Missing-valid one-coordinate change gives
   AdmissibleRestorationStep;
6. that edge bridges to OnePointRecolor on the colored induced graph;
7. that edge yields the existing SingletonKempeMove theorem;
8. two contexts share exactly the same coordinate carrier and the combined
   transport-admissibility filter behaves as intended.
```

Keep the fixture small. Do not encode W9.

## Task 13 — axiom audit

Add:

```text
DkMathTest/Tromino/RestorationRepairStateAxiomAudit.lean
```

Audit at least:

```text
coordinate-step symmetry
admissible-restoration-step symmetry
partial coloring construction / validity theorem
coordinate step -> OnePointRecolor bridge
admissible restoration edge -> SingletonKempeMove bridge
transport-admissibility filter theorem
```

No new axiom declarations.

## Explicit non-goals

Do not implement or claim:

```text
safe-candidate ranking
repair search / BFS
a concrete W9 state table
a concrete topology flip operator if none exists in production
that child admissibility implies parent admissibility
that every preserving flip is transport-compatible
cross-topology repair-height monotonicity
childHeight <= parentHeight
height-label preservation
the six OBS-019 sectors as a universal theorem
Four Color Theorem
```

Do not modify the Port triangulation/reduction theorem chain.

## Validation

From `lean/dk_math` run:

```text
lake build DkMath.Tromino.RestorationRepairState
lake build DkMathTest.Tromino.RestorationRepairStateRegression
lake build DkMathTest.Tromino.RestorationRepairStateAxiomAudit
lake build DkMath.Tromino.KempeRepair
lake build DkMath.Tromino.StateProjectionTransport
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
unsafe
```

Record warnings separately from failures.

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-005.md
```

Record:

```text
overall Outcome A / B / C
files changed
RestorationContext representation
realize definition
ProperOnColored definition
MissingAt definition
MissingValid definition
RestorationAdmissible definition
CoordinateOnePointStep definition
admissible step symmetry theorem
colored induced graph representation
partial-coloring-to-Coloring bridge
coordinate step -> OnePointRecolor theorem
admissible edge -> SingletonKempeMove theorem
parent/child combined admissibility API
regression results
axiom audit
build results
git diff --check
forbidden-token scan
deviations
exact remaining requirements for a real topology-flip provider
```

Outcome A:

```text
the partial restoration state and Missing-valid semantics are production
formalized;
admissible one-coordinate edges bridge to existing singleton Kempe theory;
the next checkpoint may attempt a topology-flip transport provider.
```

Outcome B:

```text
partial state / Missing-valid is complete but the induced-graph Coloring
bridge needs API repair, or vice versa; preserve the completed half and
report the exact obstruction.
```

Outcome C:

```text
the current total-coloring Kempe API cannot soundly receive the partial
restoration state through an induced colored graph; report the exact type/API
obstruction rather than pretending remaining vertices are colored.
```
